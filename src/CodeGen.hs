{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE QuasiQuotes               #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE ViewPatterns              #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE BlockArguments #-}
-- | Here we aim to analyze the schema.
module CodeGen(GenerateOpts(..), parserCodegen, codegen) where

import           Prelude                           hiding (id, lookup)

import Data.String.Conversions
import           Control.Monad
import qualified Data.ByteString.Builder           as B
import qualified Data.ByteString.Char8             as BS
import           Data.Default                      as Def
import qualified Data.Map.Strict                   as Map
import           Data.Maybe
import qualified Data.Set                          as Set
import qualified Language.Haskell.TH               as TH
import           Text.InterpolatedString.Perl6     (qc, ShowQ (..))
#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup((<>))
#endif

import           FromXML                           (XMLString)

import           BaseTypes
import           CodeGenMonad
import           Schema
import           TypeDecls
import           Errors(parseErrorBs)

import qualified Data.Text.Lazy.Encoding as TLE
import qualified Data.Text.Lazy as TL
import Debug.Trace (trace)
import GHC.Stack (HasCallStack)
import Control.Monad.Writer (Writer, MonadWriter (..), execWriter)
import Control.Monad.Reader
import qualified Data.List as List
import qualified Control.Lens as Lens
import Control.Lens
import Identifiers (normalizeFieldName, normalizeTypeName)
import Data.Foldable (for_)
import TypeDecls1 (TypeDecl (..), SumType)
import qualified Data.List.NonEmpty as NE
import Text.Pretty.Simple ()
import Data.Bifunctor (Bifunctor(..))

--import           Debug.Pretty.Simple
--import           Text.Pretty.Simple
--import           Identifiers


-- | Options for generating
data GenerateOpts = GenerateOpts
    { isGenerateMainFunction :: Bool
    , isUnsafe               :: Bool
    } deriving Show

instance ShowQ B.Builder where
  showQ = TL.unpack . TLE.decodeUtf8 . B.toLazyByteString

instance Def.Default GenerateOpts where
    def = GenerateOpts False False


codegen' :: Schema -> CG () -> IO String
codegen' sch gen = do
    let output = runCodeGen sch gen
    codeLines <- mapM outputToString output
    return $ unlines codeLines
  where
    outputToString (CGCodeLine cmt) = return cmt
    outputToString (CGDec decl') = do
        decl <- TH.runQ decl'
        return $ concat ["\n", TH.pprint decl, "\n"]
    outputToString (CGDecs decl') = do
        decl <- TH.runQ decl'
        return $ concat ["\n", TH.pprint decl, "\n"]

-- | Make parser for schema
parserCodegen :: GenerateOpts -> Schema -> IO String
parserCodegen opts sch = do
    --putStrLn "~~~~~~ Schema: ~~~~~~~~~"
    --pPrint sch
    --putStrLn "~~~~~~ Schema tops: ~~~~~~~~~"
    --pPrint (tops sch)
    --putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~"
    codegen' sch $ do
      -- generateParser1 opts sch
      generateParser2 True opts sch
      pure ()

-- | Eliminate duplicates from the list
-- TODO use from library
-- uniq :: Ord a => [a] -> [a]
-- uniq  = Set.toList . Set.fromList

-- * Debugging
-- tracer :: String -> p2 -> p2
--tracer lbl a = trace (lbl <> show a) a
--tracer _ a = a


-- * ----------------------------------------------------------------------------------------------
-- * ----------------------------------------------------------------------------------------------
-- * ----------------------------------------------------------------------------------------------
-- * ----------------------------------------------------------------------------------------------


outCodeLine' :: String -> CG ()
outCodeLine' msg = do
    ind <- getIndent
    outCodeLine ((replicate ind ' ') ++ msg)


withIndent :: CG a -> CG a
withIndent act = do -- TODO use `bracket`
    incIndent
    r <- act
    decIndent
    return r

codegen :: GenerateOpts -> Schema -> IO String
codegen c sch = codegen' sch $ generateParser2 False c sch

generateParser2 :: Bool -> GenerateOpts -> Schema -> CG ()
generateParser2 genParser opts@GenerateOpts{isGenerateMainFunction} schema = do
    generateModuleHeading opts
    schemaTypesMap .= schema.types
    processSchemaNamedTypes schema.types
    topNames <- forM schema.tops \el -> processType (eName el) (eType el)
    declaredTypes <- Lens.use typeDecls
    forM_ declaredTypes \case
      Alg rec -> declareAlgebraicType rec
      Newtype (t, c, wt) -> declareNewtype t c wt
      Sumtype sumtype -> declareSumType sumtype
    when genParser do
      outCodeLine [qc|type TopLevel = {bld $ unHaskellTypeName $ type_ $ head topNames}|]
      outCodeLine [qc|-- PARSER --|]
      generateParserInternalStructures
      generateParserInternalArray1 opts schema
      outCodeLine ""
      outCodeLine ""
      outCodeLine "-- extr --"
      outCodeLine ""
      outCodeLine ""
      generateParserExtractTopLevel1 opts topNames
      outCodeLine ""
      outCodeLine ""
      outCodeLine "-- parser --"
      outCodeLine ""
      outCodeLine ""
      generateParserTop
      generateAuxiliaryFunctions
      when isGenerateMainFunction $ generateMainFunction opts


  
generateParserInternalStructures :: CG ()
generateParserInternalStructures = do
    outCodeLine [qc|-- | Internal representation of TopLevel|]
    outCodeLine [qc|data TopLevelInternal = TopLevelInternal !ByteString !(V.Vector Int) deriving (G.Generic, NFData, Show)|] -- TODO qualify all imports to avoid name clush
    outCodeLine ""

eltToRepeatedness :: Element -> Repeatedness
eltToRepeatedness (Element 0 Unbounded     _ _ _) = RepMany
eltToRepeatedness (Element 0 (MaxOccurs 1) _ _ _) = RepMaybe
eltToRepeatedness (Element 0 _             _ _ _) = RepMany
eltToRepeatedness (Element 1 (MaxOccurs 1) _ _ _) = RepOnce
eltToRepeatedness (Element 1 _             _ _ _) = RepMany
eltToRepeatedness (Element m Unbounded     _ _ _) = RepNotLess m
eltToRepeatedness (Element m (MaxOccurs n) _ _ _) = RepRange m n


generateParserInternalArray1 :: GenerateOpts -> Schema -> CG ()
generateParserInternalArray1 GenerateOpts{isUnsafe} Schema{tops} = do
    outCodeLine [qc|-- PARSER --|]
    -- FIXME: examine which element is on the toplevel, if there are many
    when (length tops /= 1) $
      error $ "Only one element supported on toplevel: " <> show (map eName tops)
    let topEl = head tops
    -- Generate parser header
    let topTag = eName topEl
        topName' = unHaskellTypeName $ mkHaskellTypeName topTag
        topName = bld topName'
    when (minOccurs topEl /= 1) $ parseErrorBs topName' [qc|Wrong minOccurs = {minOccurs topEl}|]
    when (maxOccurs topEl /= MaxOccurs 1) $ parseErrorBs topName' [qc|Wrong maxOccurs = {maxOccurs topEl}|]
    outCodeLine' [qc|parseTopLevelToArray :: ByteString -> Either String TopLevelInternal|]
    outCodeLine' [qc|parseTopLevelToArray bs = Right $ TopLevelInternal bs $ V.create $ do|]
    withIndent $ do
        outCodeLine' [qc|vec <- {vecNew} ((max 1 (BS.length bs `div` 7)) * 2)|] -- TODO add code to strip vector
        outCodeLine' [qc|farthest    <- STRef.newSTRef 0 -- farthest index so far|]
        outCodeLine' [qc|farthestTag <- STRef.newSTRef ("<none>" :: ByteString)|]
        outCodeLine' [qc|let|]
        withIndent $ do
            --outCodeLine' [qc|parse{topName} :: forall s . UMV.STVector s Int -> ST s ()|]
            outCodeLine' [qc|parse{topName} vec = do|]
            withIndent $ do
                outCodeLine' [qc|{vecWrite} vec (0::Int) (0::Int)|]
                outCodeLine' [qc|(_, _) <- inOneTag "{topTag}" 0 (skipSpaces $ skipHeader $ skipSpaces 0) parse{topName}Content|]
                outCodeLine' [qc|return ()|]
                outCodeLine' [qc|where|]
                parseFuncs_ <- Lens.use parseFunctions
                withIndent $ do
                    mapM_ generateFunction parseFuncs_
                    generateAuxiliaryFunctionsIA
        outCodeLine' [qc|parse{topName} vec|]
        outCodeLine' [qc|return vec|]
  where
    vecNew, vecWrite, bsIndex :: String
    vecNew   | isUnsafe  = "V.unsafeNew"
             | otherwise = "V.new"
    vecWrite | isUnsafe  = "V.unsafeWrite"
             | otherwise = "V.write"
    bsIndex  | isUnsafe  = "BSU.unsafeIndex"
             | otherwise = "BS.index"
    generateAuxiliaryFunctionsIA = do
        --
        -- TODO read this from file!
        --
        outCodeLine' [qc|toError tag strOfs act = do|]
        outCodeLine' [qc|    act >>= \case|]
        outCodeLine' [qc|        Nothing -> failExp ("<" <> tag) strOfs|]
        outCodeLine' [qc|        Just res -> return res|]
        outCodeLine' [qc|getTagName :: Int -> XMLString|]
        outCodeLine' [qc|getTagName strOfs = BS.takeWhile (\c -> not (isSpaceChar c || c == closeTagChar || c == slashChar)) $ BS.drop (skipToOpenTag strOfs + 1) bs|]
        outCodeLine' [qc|getAttrName :: Int -> XMLString|]
        outCodeLine' [qc|getAttrName strOfs = BS.takeWhile (/= eqChar) $ BS.drop strOfs bs|]
        outCodeLine' [qc|inOneTag          tag arrOfs strOfs inParser = toError tag strOfs $ inOneTag' True tag arrOfs strOfs inParser|]
        outCodeLine' [qc|inOneTagWithAttrs attrAlloc attrRouting tag arrOfs strOfs inParser =|]
        outCodeLine' [qc|  toError tag strOfs $ inOneTagWithAttrs' attrAlloc attrRouting tag arrOfs strOfs inParser|]
        outCodeLine' [qc|inOneTagWithAttrs' attrAlloc attrRouting tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    let tagStrOfs = skipToOpenTag strOfs + 1|]
        outCodeLine' [qc|    q <- parseTagWithAttrs attrAlloc attrRouting tag arrOfs tagStrOfs|]
        outCodeLine' [qc|    case q of|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag tagStrOfs|]
        outCodeLine' [qc|            return Nothing|]
        outCodeLine' [qc|        Just ((ofs', arrOfs'), True) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser arrOfs' (ofs' - 1)|]
        outCodeLine' [qc|            return $ Just (arrOfs, ofs')|]
        outCodeLine' [qc|        Just ((ofs', arrOfs'), False) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser arrOfs' ofs'|]
        outCodeLine' [qc|            let ofs'' = skipToOpenTag strOfs|]
        outCodeLine' [qc|            if bs `BSU.unsafeIndex` (ofs'' + 1) == slashChar then do|]
        outCodeLine' [qc|                case ensureTag False tag (ofs'' + 2) of|]
        outCodeLine' [qc|                    Nothing     -> do|]
        outCodeLine' [qc|                        updateFarthest tag tagStrOfs|]
        outCodeLine' [qc|                        return Nothing|]
        outCodeLine' [qc|                    Just (ofs''', _) -> return $ Just (arrOfs, ofs''')|]
        outCodeLine' [qc|            else do|]
        outCodeLine' [qc|                return Nothing|]
        outCodeLine' [qc|inOneTag' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    let tagOfs = skipToOpenTag strOfs + 1|]
        outCodeLine' [qc|    case ensureTag hasAttrs tag tagOfs of|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag tagOfs|]
        outCodeLine' [qc|            return Nothing|]
        outCodeLine' [qc|        Just (ofs', True) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser arrOfs (ofs' - 1)|] -- TODO points to special unparseable place
        outCodeLine' [qc|            return $ Just (arrOfs, ofs')|]
        outCodeLine' [qc|        Just (ofs', _) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser arrOfs ofs'|]
        outCodeLine' [qc|            let ofs'' = skipToOpenTag strOfs|]
        outCodeLine' [qc|            if bs `{bsIndex}` (ofs'' + 1) == slashChar then do|]
        outCodeLine' [qc|                case ensureTag False tag (ofs'' + 2) of|]
        outCodeLine' [qc|                    Nothing     -> do|]
        outCodeLine' [qc|                        updateFarthest tag tagOfs|]
        outCodeLine' [qc|                        return Nothing|]
        outCodeLine' [qc|                    Just (ofs''', _) -> return $ Just (arrOfs, ofs''')|]
        outCodeLine' [qc|            else do|]
        outCodeLine' [qc|                return Nothing|]
        -- ~~~~~~~~
        outCodeLine' [qc|inMaybeTag tag arrOfs strOfs inParser = inMaybeTag' True tag arrOfs strOfs inParser|]
        outCodeLine' [qc|inMaybeTagWithAttrs tag arrOfs strOfs inParser = inMaybeTagWithAttrs' tag arrOfs strOfs inParser|]
        outCodeLine' [qc|inMaybeTagWithAttrs' attrAlloc attrRouting tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    V.unsafeWrite vec arrOfs 1|]
        outCodeLine' [qc|    inOneTagWithAttrs' attrAlloc attrRouting tag (arrOfs + 1) strOfs inParser >>= \case|]
        outCodeLine' [qc|        Just res -> return res|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag strOfs|]
        outCodeLine' [qc|            {vecWrite} vec arrOfs 0|]
        outCodeLine' [qc|            return (arrOfs +11, strOfs)|]
        outCodeLine' [qc|inMaybeTag' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    V.unsafeWrite vec arrOfs 1|]
        outCodeLine' [qc|    inOneTag' hasAttrs tag (arrOfs + 1) strOfs inParser >>= \case|]
        outCodeLine' [qc|        Just res -> return res|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag strOfs|]
        outCodeLine' [qc|            {vecWrite} vec arrOfs 0|]
        outCodeLine' [qc|            return (arrOfs + 1, strOfs)|]
        outCodeLine' [qc|inManyTags tag arrOfs strOfs inParser = inManyTags' True tag arrOfs strOfs inParser|]
        outCodeLine' [qc|inManyTagsWithAttrs tag arrOfs strOfs inParser = inManyTagsWithAttrs' tag arrOfs strOfs inParser|]
        --outCodeLine' [qc|inManyTags' :: Bool -> ByteString -> Int -> Int -> (Int -> Int -> ST s (Int, Int)) -> ST s (Int, Int)|]
        outCodeLine' [qc|inManyTags' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    (cnt, endArrOfs, endStrOfs) <- flip fix (0, (arrOfs + 1), strOfs) $ \next (cnt, arrOfs', strOfs') ->|]
        outCodeLine' [qc|        inOneTag' hasAttrs tag arrOfs' strOfs' inParser >>= \case|]
        outCodeLine' [qc|            Just (arrOfs'', strOfs'') -> next   (cnt + 1, arrOfs'', strOfs'')|]
        outCodeLine' [qc|            Nothing                   -> do|]
        outCodeLine' [qc|                updateFarthest tag strOfs|]
        outCodeLine' [qc|                return (cnt,     arrOfs', strOfs')|]
        outCodeLine' [qc|    {vecWrite} vec arrOfs cnt|]
        outCodeLine' [qc|    return (endArrOfs, endStrOfs)|]
        outCodeLine' [qc|inManyTagsWithAttrs' attrAlloc attrRouting tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    (cnt, endArrOfs, endStrOfs) <- flip fix (0, (arrOfs + 1), strOfs) $ \next (cnt, arrOfs', strOfs') ->|]
        outCodeLine' [qc|        inOneTagWithAttrs' attrAlloc attrRouting tag arrOfs' strOfs' inParser >>= \case|]
        outCodeLine' [qc|            Just (arrOfs'', strOfs'') -> next   (cnt + 1, arrOfs'', strOfs'')|]
        outCodeLine' [qc|            Nothing                   -> do|]
        outCodeLine' [qc|                updateFarthest tag strOfs|]
        outCodeLine' [qc|                return (cnt,     arrOfs', strOfs')|]
        outCodeLine' [qc|    {vecWrite} vec arrOfs cnt|]
        outCodeLine' [qc|    return (endArrOfs, endStrOfs)|]

        -- ~~~~~~~~
        -- возвращает вторым параметром True если перед закрытием тега идет '/'
        outCodeLine' [qc|ensureTag True expectedTag ofs|]
        outCodeLine' [qc|  | expectedTag `BS.isPrefixOf` (BS.drop ofs bs) =|]
        outCodeLine' [qc|      if bs `{bsIndex}` ofsToEnd == closeTagChar|]
        outCodeLine' [qc|        then Just (ofsToEnd + 1, False)|]
        outCodeLine' [qc|      else if isSpaceChar (bs `{bsIndex}` ofsToEnd)|]
        outCodeLine' [qc|        then let ofs' = skipToCloseTag (ofs + BS.length expectedTag)|]
        outCodeLine' [qc|             in Just (ofs' + 1, bs `{bsIndex}` (ofs' - 1) == slashChar)|]
        outCodeLine' [qc|      else|]
        outCodeLine' [qc|        Nothing|]
        outCodeLine' [qc|  | otherwise = Nothing|]
        outCodeLine' [qc|  where ofsToEnd = ofs + BS.length expectedTag|]
        outCodeLine' [qc|ensureTag False expectedTag ofs|]
        outCodeLine' [qc|  | expectedTag `BS.isPrefixOf` (BS.drop ofs bs) && (bs `{bsIndex}` ofsToEnd == closeTagChar)|]
        outCodeLine' [qc|        = Just (ofsToEnd + 1, False)|]
        outCodeLine' [qc|  | otherwise|]
        outCodeLine' [qc|        = Nothing|]
        outCodeLine' [qc|  where ofsToEnd = ofs + BS.length expectedTag|]
        outCodeLine' [qc|parseAttributes attrRouting strOfs arrOfs = do|]
        outCodeLine' [qc|  let ofs1 = skipSpaces strOfs|]
        outCodeLine' [qc|      curCh = bs `BSU.unsafeIndex` ofs1 |]
        outCodeLine' [qc|  if curCh == slashChar || curCh == closeTagChar|]
        outCodeLine' [qc|    then pure ofs1|]
        outCodeLine' [qc|    else do|]
        outCodeLine' [qc|    let|]
        outCodeLine' [qc|      attrName = getAttrName ofs1|]
        outCodeLine' [qc|      ofsAttrContent = ofs1 + BS.length attrName + 2|]
        outCodeLine' [qc|    attrContentEnd <- parseAttrContent (attrRouting arrOfs attrName) ofsAttrContent|]
        outCodeLine' [qc|    parseAttributes attrRouting (attrContentEnd + 1) arrOfs|]
        outCodeLine' [qc|parseTagWithAttrs attrAlloc attrRouting expectedTag arrOfs ofs|]
        outCodeLine' [qc|  | expectedTag `BS.isPrefixOf` (BS.drop ofs bs) = do|]
        outCodeLine' [qc|      arrOfsAfterAttrs <- attrAlloc arrOfs|]
        outCodeLine' [qc|      if bs `BSU.unsafeIndex` ofsToEnd == closeTagChar|]
        outCodeLine' [qc|        then pure $ Just ((ofsToEnd + 1, arrOfsAfterAttrs), False)|]
        outCodeLine' [qc|      else if isSpaceChar (bs `BSU.unsafeIndex` ofsToEnd)|]
        outCodeLine' [qc|        then do|]
        outCodeLine' [qc|          _failOfs <- STRef.readSTRef farthest|]
        outCodeLine' [qc|          strOfsAfterAttrs <- parseAttributes attrRouting ofsToEnd arrOfs|]
        outCodeLine' [qc|          let ofs' = skipToCloseTag strOfsAfterAttrs|]
        outCodeLine' [qc|          pure $ Just ((ofs' + 1, arrOfsAfterAttrs), bs `BSU.unsafeIndex` (ofs' - 1) == slashChar)|]
        outCodeLine' [qc|      else|]
        outCodeLine' [qc|        pure Nothing|]
        outCodeLine' [qc|  | otherwise = pure Nothing|]
        outCodeLine' [qc|  where ofsToEnd = ofs + BS.length expectedTag|]


        outCodeLine' [qc|failExp _expStr _ofs = do|]
        outCodeLine' [qc|  failOfs <- STRef.readSTRef farthest|]
        outCodeLine' [qc|  failTag <- STRef.readSTRef farthestTag|]
        outCodeLine' [qc|  let failActual = substr bs failOfs (BS.length failTag + 10)|]
        outCodeLine' [qc|  parseError failOfs bs (BSC.unpack $ "Expected tag '" <> failTag <> "', but got '" <> failActual <> "'")|]
        outCodeLine' [qc|updateFarthest tag tagOfs = do|]
        outCodeLine' [qc|  f <- STRef.readSTRef farthest|]
        outCodeLine' [qc|  when (tagOfs > f) $ do|]
        outCodeLine' [qc|    STRef.writeSTRef farthest    tagOfs|]
        outCodeLine' [qc|    STRef.writeSTRef farthestTag tag|]
        outCodeLine' [qc|substr :: ByteString -> Int -> Int -> ByteString|]
        outCodeLine' [qc|substr bs ofs len = BS.take len $ BS.drop ofs bs -- TODO replace with UNSAFE?|]
        outCodeLine' [qc|--|]
        --outCodeLine' [qc|parseString :: Int -> Int -> ST s (Int, Int)|]
        outCodeLine' [qc|parseXMLStringContent = parseString|]
        outCodeLine' [qc|parseAttrContent arrAttrLocation strStart = do|]
        outCodeLine' [qc|  let strEnd = skipTo dquoteChar strStart|]
        outCodeLine' [qc|  when (arrAttrLocation > 0) do|]
        outCodeLine' [qc|    V.unsafeWrite vec arrAttrLocation     strStart|]
        outCodeLine' [qc|    V.unsafeWrite vec (arrAttrLocation+1) (strEnd - strStart)|]
        outCodeLine' [qc|  return strEnd|]

        outCodeLine' [qc|parseString arrStart strStart = do|]
        outCodeLine' [qc|  let strEnd = skipToOpenTag strStart|]
        outCodeLine' [qc|  {vecWrite} vec arrStart     strStart|]
        outCodeLine' [qc|  {vecWrite} vec (arrStart+1) (strEnd - strStart)|]
        outCodeLine' [qc|  return (arrStart+2, strEnd)|]
        outCodeLine' [qc|parseScientificContent = parseString|]
        outCodeLine' [qc|parseDateTimeContent = parseString|]
        outCodeLine' [qc|parseDurationContent = parseString|]
        outCodeLine' [qc|parseIntegerContent = parseString|]
        outCodeLine' [qc|parseIntContent = parseString|]
        outCodeLine' [qc|parseInt64Content = parseString|]
        outCodeLine' [qc|parseDayContent = parseString|]
        outCodeLine' [qc|parseBooleanContent = parseString|]
        outCodeLine' [qc|skipSpaces ofs|]
        outCodeLine' [qc|  | isSpaceChar (bs `{bsIndex}` ofs) = skipSpaces (ofs + 1)|]
        outCodeLine' [qc|  | otherwise = ofs|]
        outCodeLine' [qc|isSpaceChar :: Word8 -> Bool|]
        outCodeLine' [qc|isSpaceChar c = c == 32 || c == 10 || c == 9 || c == 13|]
        outCodeLine' [qc|skipHeader :: Int -> Int|]
        outCodeLine' [qc|skipHeader ofs|]
        outCodeLine' [qc|  | bs `{bsIndex}` ofs == openTagChar && bs `{bsIndex}` (ofs + 1) == questionChar = skipToCloseTag (ofs + 2) + 1|]
        outCodeLine' [qc|  | otherwise = ofs|]
        outCodeLine' [qc|eqChar       = 61 -- '='|]
        outCodeLine' [qc|dquoteChar   = 34 -- '"'|]
        outCodeLine' [qc|slashChar    = 47 -- '<'|]
        outCodeLine' [qc|openTagChar  = 60 -- '<'|]
        outCodeLine' [qc|closeTagChar = 62 -- '>'|]
        outCodeLine' [qc|questionChar = 63 -- '?'|]
        outCodeLine' [qc|skipToCloseTag :: Int -> Int|]
        outCodeLine' [qc|skipToCloseTag ofs|]
        outCodeLine' [qc|  | bs `{bsIndex}` ofs == closeTagChar = ofs|]
        outCodeLine' [qc|  | otherwise = skipToCloseTag (ofs + 1)|]
        outCodeLine' [qc|skipToOpenTag :: Int -> Int|]
        outCodeLine' [qc|skipToOpenTag ofs|] -- TODO with `takeWhile`
        outCodeLine' [qc|  | bs `{bsIndex}` ofs == openTagChar = ofs|]
        outCodeLine' [qc|  | otherwise = skipToOpenTag (ofs + 1)|]
        outCodeLine' [qc|skipTo :: Word8 -> Int -> Int|]
        outCodeLine' [qc|skipTo c ofs|]
        outCodeLine' [qc|  | bs `BSU.unsafeIndex` ofs == c = ofs|]
        outCodeLine' [qc|  | otherwise = skipTo c (ofs + 1)|]

generateParserExtractTopLevel1 ::
  HasCallStack =>
  GenerateOpts ->
  [TypeWithAttrs] ->
  CG ()
generateParserExtractTopLevel1 GenerateOpts{isUnsafe} topTypes = do
    forM_ topTypes $ \topType -> do
        let topTypeName = bld topType.type_.unHaskellTypeName
        outCodeLine' [qc|extractTopLevel :: TopLevelInternal -> TopLevel|]
        outCodeLine' [qc|extractTopLevel (TopLevelInternal bs arr) = fst $ extract{topTypeName}Content 0|]
    withIndent $ do
        outCodeLine' "where"
        extractFuncs_ <- Lens.use extractFunctions
        withIndent $ do
            mapM_ generateFunction extractFuncs_
            generateAuxiliaryFunctions_
  where
    generateAuxiliaryFunctions_ = do
        outCodeLine' [qc|extractStringContent :: Int -> (ByteString, Int)|]
        if isUnsafe then
            outCodeLine' [qc|extractStringContent ofs = (BSU.unsafeTake bslen (BSU.unsafeDrop bsofs bs), ofs + 2)|]
        else
            outCodeLine' [qc|extractStringContent ofs = (BS.take bslen (BS.drop bsofs bs), ofs + 2)|]
        outCodeLine' [qc|  where|]
        outCodeLine' [qc|    bsofs = arr {index} ofs|]
        outCodeLine' [qc|    bslen = arr {index} (ofs + 1)|]
        outCodeLine' [qc|extractMaybe ofs subextr|]
        outCodeLine' [qc|  | arr {index} ofs == 0 = (Nothing, ofs + 1)|]
        outCodeLine' [qc|  | otherwise                     = first Just $ subextr (ofs + 1)|]
        outCodeLine' [qc|extractAttribute ofs subextr|]
        outCodeLine' [qc|  | arr `V.unsafeIndex` ofs == 0 = (Nothing, ofs + 2)|]
        outCodeLine' [qc|  | otherwise                     = first Just $ subextr ofs|]
        outCodeLine' [qc|extractMany ofs subextr = extractMany' (ofs + 1) (arr {index} ofs)|]
        outCodeLine' [qc|  where|]
        outCodeLine' [qc|    extractMany' ofs 0   = ([], ofs)|]
        outCodeLine' [qc|    extractMany' ofs len =|]
        outCodeLine' [qc|      let (v, ofs') = subextr ofs|]
        outCodeLine' [qc|      in first (v:) $ extractMany' ofs' (len - 1)|]
        outCodeLine' [qc|extractTokenContent = extractStringContent|]
        outCodeLine' [qc|extractXMLStringContent = extractStringContent|]
        outCodeLine' [qc|extractDateTimeContent :: Int -> (ZonedTime, Int)|]
        outCodeLine' [qc|extractDateTimeContent = extractAndParse zonedTimeStr|]
        outCodeLine' [qc|extractDayContent :: Int -> (Day, Int)|]
        outCodeLine' [qc|extractDayContent = extractReadInst|]
        outCodeLine' [qc|extractDurationContent :: Int -> (Duration, Int)|]
        outCodeLine' [qc|extractDurationContent = extractAndParse parseDuration|]
        outCodeLine' [qc|extractScientificContent :: Int -> (Scientific, Int)|]
        outCodeLine' [qc|extractScientificContent = extractReadInst|]
        outCodeLine' [qc|extractIntegerContent :: Int -> (Integer, Int)|]
        outCodeLine' [qc|extractIntegerContent = extractReadInst|]
        outCodeLine' [qc|extractIntContent :: Int -> (Int, Int)|]
        outCodeLine' [qc|extractIntContent = extractReadInst|]
        outCodeLine' [qc|extractInt64Content :: Int -> (Int64, Int)|]
        outCodeLine' [qc|extractInt64Content = extractReadInst|]
        outCodeLine' [qc|extractBoolContent :: Int -> (Bool, Int)|]
        outCodeLine' [qc|extractBoolContent ofs = first (\case|]
        outCodeLine' [qc|    "true" -> True|]
        outCodeLine' [qc|    "1"    -> True|]
        outCodeLine' [qc|    _      -> False|]
        outCodeLine' [qc|    ) $ extractStringContent ofs|]
        outCodeLine' [qc|first f (a,b) = (f a, b)|]
        outCodeLine' [qc|extractAndParse :: (ByteString -> Either String a) -> Int -> (a, Int)|]
        outCodeLine' [qc|extractAndParse parser ofs = first (catchErr ofs parser) $ extractStringContent ofs|]
        outCodeLine' [qc|extractReadInst :: (Read a) => Int -> (a, Int)|]
        outCodeLine' [qc|extractReadInst = extractAndParse readEither|]
        outCodeLine' [qc|catchErr :: Int -> (ByteString -> Either String b) -> ByteString -> b|]
        outCodeLine' [qc|catchErr ofs f str = either (\msg -> parseError bsofs bs msg) id (f str)|]
        outCodeLine' [qc|  where bsofs = arr {index} ofs|]
        outCodeLine' [qc|readEither :: Read a => ByteString -> Either String a|]
        outCodeLine' [qc|readEither str =|]
        outCodeLine' [qc|    case reads (BSC.unpack str) of|]
        outCodeLine' [qc|        [(a, [])] -> Right a|]
        outCodeLine' [qc|        _ -> Left $ "Can't parse " ++ show str|]
    index | isUnsafe  = "`V.unsafeIndex`" :: String
          | otherwise = "V.!"


generateAuxiliaryFunctions :: CG ()
generateAuxiliaryFunctions = do
    outCodeLine' ""
    outCodeLine' ""
    outCodeLine' [qc|zonedTimeStr :: ByteString -> Either String ZonedTime|]
    outCodeLine' [qc|zonedTimeStr str =|]
    outCodeLine' [qc|    case (readP_to_S (readPTime True defaultTimeLocale fmt) $ BSC.unpack str) of|]
    outCodeLine' [qc|        [(dt, [])] -> Right dt|]
    outCodeLine' [qc|        _          -> Left ("Can't parse " ++ show str)|]
    outCodeLine' [qc|  where|]
    outCodeLine' [qc|    fmt = iso8601DateFormat (Just "%H:%M:%S%Q%Z")|]
    outCodeLine' "{-# INLINE zonedTimeStr #-}"
    outCodeLine' ""
    -- `fromRight` appears only in base 4.10, and not available on GHC 8.0, so we use own
    outCodeLine' [qc|fromRight' :: b -> Either a b -> b|]
    outCodeLine' [qc|fromRight' _ (Right b) = b|]
    outCodeLine' [qc|fromRight' b _         = b|]
    outCodeLine' "{-# INLINE fromRight' #-}"
    outCodeLine' ""
    outCodeLine' ""

generateParserTop :: CG ()
generateParserTop = do
    outCodeLine "parse :: ByteString -> Either String TopLevel" -- TODO
    outCodeLine "parse = fmap extractTopLevel . parseTopLevelToArray"

generateMainFunction :: HasCallStack => GenerateOpts -> CG ()
generateMainFunction GenerateOpts{..} = trace "main" do
    outCodeLine' [qc|parseAndPrintFiles :: Bool -> [FilePath] -> IO ()|]
    outCodeLine' [qc|parseAndPrintFiles isPrinting filenames =|]
    withIndent $ do
        outCodeLine' [qc|forM_ filenames $ \filename -> do|]
        withIndent $ do
            outCodeLine' [qc|file <- BS.readFile filename|]
            outCodeLine' [qc|case parse file of|]
            withIndent $ do
                outCodeLine' [qc|Left err -> do|]
                withIndent $ do
                    outCodeLine' [qc|hPutStrLn stderr $ "Error while parsing \"" ++ filename ++ "\": " ++ err|]
                    outCodeLine' [qc|exitFailure|]
                outCodeLine' [qc|Right result -> do|]
                withIndent $ do
                    outCodeLine' [qc|if isPrinting then do|]
                    withIndent $ do
                        outCodeLine' [qc|putStrLn filename|]
                        if isUnsafe then
                            outCodeLine' [qc|pPrint result|]
                        else
                            outCodeLine' [qc|print result|]
                    outCodeLine' [qc|else do|]
                    withIndent $ do
                        outCodeLine' [qc|result `seq` Prelude.putStrLn $ "Successfully parsed " ++ filename|]
    outCodeLine' ""
    outCodeLine' "main :: IO ()"
    outCodeLine' "main = do"
    withIndent $ do
        outCodeLine' [qc|args <- getArgs|]
        outCodeLine' [qc|case Data.List.partition (== "--print") args of|]
        withIndent $ do
            outCodeLine' [qc|([], filenames) -> parseAndPrintFiles False filenames|]
            outCodeLine' [qc|(_,  filenames) -> parseAndPrintFiles True  filenames|]
        outCodeLine' "exitSuccess"
    outCodeLine' ""
    outCodeLine' [qc|echo :: Show a => String -> a -> a|]
    outCodeLine' [qc|echo msg x = (msg <> ": "<> show x) `trace` x |]

getSequenceAttrs :: SequenceGI -> AttributesInfo
getSequenceAttrs s = case NE.nonEmpty $ map (.xmlName) s.attributes of
  Nothing -> NoAttrs
  Just a -> AttributesInfo a

getExtContentAttrs :: ContentWithAttrsGI -> AttributesInfo
getExtContentAttrs c = case NE.nonEmpty $ map (.xmlName) c.attributes of
  Nothing -> NoAttrs
  Just a -> AttributesInfo a

mkChoiceTypeDeclaration :: ChoiceGI -> SumType
mkChoiceTypeDeclaration ch =
  ( TyData $ bld ch.typeName.unHaskellTypeName
  , flip map ch.alts \(_eltName, cons_, conType) -> do
    (TyCon $ bld cons_.unHaskellConsName, TyType $ bld conType.type_.unHaskellTypeName)
  )

mkSequenceTypeDeclaration :: SequenceGI -> (TyData, [Record])
mkSequenceTypeDeclaration s =
  (TyData $ B.byteString s.typeName.unHaskellTypeName
  , [(TyCon $ B.byteString s.consName.unHaskellConsName, map mkFieldDeclaration $ s.attributes <> s.fields)]
  )

mkAttrContentTypeDeclaration :: ContentWithAttrsGI -> (TyData, [Record])
mkAttrContentTypeDeclaration cgi =
  ( TyData $ B.byteString cgi.typeName.unHaskellTypeName
  , [ ( TyCon $ B.byteString cgi.consName.unHaskellConsName
      , map mkFieldDeclaration $ cgi.attributes <> [contentField]
      )
    ]
  )
  where
  contentField :: FieldGI
  contentField =
    -- TODO: maybe it's not the best idea to use FieldGI here
    FieldGI
      { haskellName = "content"
      , xmlName = "abra-schwabra-kadabra" -- should be never used
      , cardinality = RepOnce
      , typeName = typeNoAttrs cgi.contentType GBaseType
      }


mkFieldDeclaration :: FieldGI -> TyField
mkFieldDeclaration fld =
  ( TyFieldName $ B.byteString fld.haskellName.unHaskellFieldName
  , TyType $ mkCardinality $ B.byteString fld.typeName.type_.unHaskellTypeName
  )
  where
    mkCardinality x = case fld.cardinality of
      RepMaybe -> "Maybe " <> x
      RepOnce -> x
      _ -> "[" <> x <> "]"

exampleSequenceGI :: SequenceGI
exampleSequenceGI = SequenceGI
  { typeName = "TestType"
  , consName = "TestCons"
  , attributes = []
  , fields =
    [ FieldGI "departure" "departureElt" RepMaybe $ typeNoAttrs "String" GBaseType
    , FieldGI "arrival" "arrivalElt" RepOnce $ typeNoAttrs "Int" GBaseType
    , FieldGI "techStops" "techStopsElt" RepMany $ typeNoAttrs "TechStop" GBaseType
    ]
  }

type CodeWriter' = ReaderT Int (Writer [String])
type CodeWriter = CodeWriter' ()

runCodeWriter :: CodeWriter -> [String]
runCodeWriter action = execWriter $ runReaderT action 0

generateFunction :: FunctionBody -> CG ()
generateFunction = mapM_ outCodeLine' . unFunctionBody

out1 :: String -> CodeWriter 
out1 str = do
  offset <- ask
  tell . (:[]) $ replicate (2*offset) ' ' <> str

withIndent1 :: CodeWriter -> CodeWriter
withIndent1 = local (+1)

getParserNameForType :: HaskellTypeName -> String
getParserNameForType type_ = 
  "parse" <> cs type_.unHaskellTypeName <> "Content"

bld :: XMLString -> B.Builder
bld = B.byteString

generateAttrContentParse :: ContentWithAttrsGI -> FunctionBody
generateAttrContentParse cgi = FunctionBody $ runCodeWriter do
  generateAttrsAllocation
    TypeWithAttrs {type_ = cgi.typeName, attrs = getExtContentAttrs cgi, giType = GAttrContent cgi}
  out1 (getParserNameForType cgi.typeName <> " = " <> getParserNameForType cgi.contentType)

generateSequenceParseFunctionBody :: SequenceGI -> FunctionBody
generateSequenceParseFunctionBody s = FunctionBody $ runCodeWriter do
  generateAttrsAllocation
    TypeWithAttrs { type_ = s.typeName, attrs = getSequenceAttrs s, giType = GSeq s }
  out1 (getParserNameForType s.typeName <> " arrStart strStart = do")
  withIndent1 do
    let (arrStart, strStart) = ("arrStart", "strStart")
        fields = {- s.attributes <> -} s.fields
    let ofsNames' = ((arrStart, strStart) : [ ( [qc|arrOfs{i}|], [qc|strOfs{i}|]) | i <- [(1::Int)..]])
                    :: [(XMLString, XMLString)]
        ofsNames = zip ofsNames' (tail ofsNames')
        (arrRet, strRet) = bimap bld bld $ ofsNames' !! length fields
    forM_ (zip ofsNames fields) $ \((oldOffsets, (arrOfs', strOfs')), field) -> do
      out1 [qc|({arrOfs'}, {strOfs'}) <- do|]
      withIndent1 do
        -- offsetsAfterAllocGen <- generateAttrsAllocation oldOffsets field.typeName
        generateParseElementCall oldOffsets field
    out1 [qc|pure ({arrRet}, {strRet})|]

generateAttrsAllocation ::
  TypeWithAttrs ->
  CodeWriter
generateAttrsAllocation TypeWithAttrs{type_, attrs = attrInfo} =
  withPresentAttrs \attrs -> do
    let attrsNum = length attrs
    let totalAllocLen = 2*attrsNum
    out1 [qc|{getAttrsAllocatorName type_} ofs = do|]
    withIndent1 do
      out1 [qc|forM_ [0..{totalAllocLen - 1}] $ \i -> V.unsafeWrite vec (ofs + i) 0|]
      out1 [qc|pure $ ofs + {totalAllocLen}|]
    out1 [qc|{getAttrsRoutingName type_} ofs = \case|]
    withIndent1 $ do
      forM_ (zip [0::Int, 2 .. ] $ NE.toList attrs) \(ofs, attr) ->
        out1 [qc|"{attr}" -> ofs + {ofs}|]
      out1 [qc|_ -> (-1)|]
  where
  withPresentAttrs action = case attrInfo of
    NoAttrs -> pure ()
    AttributesInfo neStr -> action neStr

generateParseElementCall :: (XMLString, XMLString) -> FieldGI -> CodeWriter
generateParseElementCall (arrOfs, strOfs) field = do
  let parsedType = field.typeName.type_
      parserName = getParserNameForType parsedType
      hasAttrs = field.typeName.attrs /= NoAttrs
      (allocator :: B.Builder, tagQModifier) =
        if hasAttrs
        then ([qc|{getAttrsAllocatorName parsedType} {getAttrsRoutingName parsedType} |], (<> "WithAttrs"))
        else ("", identity)
  let tagQuantifier::XMLString = case field.cardinality of
          RepMaybe -> "inMaybeTag"
          RepOnce  -> "inOneTag"
          _        -> "inManyTags"
      tagName = field.xmlName
  out1 [qc|{tagQModifier tagQuantifier} {allocator}"{tagName}" {arrOfs} {strOfs} {parserName}|]

getAttrsRoutingName :: HaskellTypeName -> XMLString
getAttrsRoutingName t = [qc|get{bld $ unHaskellTypeName t}AttrOffset|]

getAttrsAllocatorName :: HaskellTypeName -> XMLString
getAttrsAllocatorName t = [qc|allocate{bld $ unHaskellTypeName t}Attrs|]

generateChoiceParseFunctionBody :: ChoiceGI -> FunctionBody
generateChoiceParseFunctionBody ch = FunctionBody $ runCodeWriter $
  out1 (getParserNameForType ch.typeName <> " arrStart strStart = do") >> withIndent1 do
    out1 [qc|let tagName = getTagName strStart|]
    out1 [qc|case tagName of|]
    withIndent1 $ forM_ (zip ch.alts [0 :: Int ..]) \((altTag, _cons, type_), altIdx) -> do
      let altParser = getParserNameForType type_.type_
          vecWrite {- | isUnsafe -} = "V.unsafeWrite" :: B.Builder
      out1 [qc|"{altTag}" -> {vecWrite} vec arrStart {altIdx} >> inOneTag "{altTag}" (arrStart+1) strStart {altParser}|]

generateChoiceExtractFunctionBody :: ChoiceGI -> FunctionBody
generateChoiceExtractFunctionBody ch = FunctionBody $ runCodeWriter do
  let chName = bld ch.typeName.unHaskellTypeName
  out1 [qc|extract{chName}Content ofs = do|]
  withIndent1 do
    let vecIndex = "`V.unsafeIndex`" :: String
    out1 [qc|let altIdx = arr {vecIndex} ofs|]
    out1 [qc|case altIdx of|]
    withIndent1 $ forM_ (zip ch.alts [0 :: Int ..]) \((_altTag, cons_, type_), altIdx) -> do
      let consBld = bld cons_.unHaskellConsName
          typeBld = bld type_.type_.unHaskellTypeName
      out1 [qc|{altIdx} -> first {consBld} $ extract{typeBld}Content (ofs + 1)|]

generateAttrContentExtract :: ContentWithAttrsGI -> FunctionBody
generateAttrContentExtract cgi = FunctionBody $ runCodeWriter do
  let recType = bld cgi.typeName.unHaskellTypeName
  let baseType = bld cgi.contentType.unHaskellTypeName
  let attrNum = length cgi.attributes
  let consName = bld cgi.consName.unHaskellConsName
  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 $ do
    forM_ (zip cgi.attributes [1..attrNum]) $ \(attr, aIdx) -> do
        let oldOfs = if aIdx == 1 then "ofs" :: XMLString else [qc|ofs{aIdx-1}|]
        let haskellAttrName = attr.haskellName.unHaskellFieldName
        let haskellTypeName = bld attr.typeName.type_.unHaskellTypeName
        out1 [qc|let ({bld haskellAttrName}, ofs{aIdx}) = extractAttribute {oldOfs} extract{haskellTypeName}Content in|]
    out1 [qc|let (content, ofs{attrNum + 1}) = extract{baseType}Content ofs{attrNum} in|]
    out1 [qc|({consName}\{..}, ofs{attrNum + 1})|]

generateSequenceExtractFunctionBody :: SequenceGI -> FunctionBody
generateSequenceExtractFunctionBody s = FunctionBody $ runCodeWriter do
  let recType = bld s.typeName.unHaskellTypeName
  let attrNum = length s.attributes
  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 $ do
      attrFields <- forM (zip s.attributes [1..attrNum]) $ \(attr, aIdx) -> do
          let oldOfs = if aIdx == 1 then "ofs" :: XMLString else [qc|ofs{aIdx-1}|]
          let haskellAttrName = attr.haskellName.unHaskellFieldName
          let haskellTypeName = bld attr.typeName.type_.unHaskellTypeName
          out1 [qc|let ({bld haskellAttrName}, ofs{aIdx}) = extractAttribute {oldOfs} extract{haskellTypeName}Content in|]
          return haskellAttrName
      properFields <- forM (zip s.fields [(attrNum + 1)..]) $ \(fld, ofsIdx::Int) -> do
              let ofs = if ofsIdx == 1 then ("ofs"::XMLString) else [qc|ofs{ofsIdx - 1}|]
                  fieldName = fld.haskellName.unHaskellFieldName
                  extractor = getExtractorNameWithQuant ofs fld
              out1 [qc|let ({bld fieldName}, ofs{ofsIdx}) = {extractor} in|]
              return fieldName
      let fields = attrFields ++ properFields
          ofs' = if null fields then "ofs" else [qc|ofs{length fields}|]::XMLString
          haskellConsName = s.consName.unHaskellConsName
      case fields of
          []         -> out1 [qc|({haskellConsName}, {ofs'})|]
          [oneField] -> out1 [qc|({haskellConsName} {oneField}, {ofs'})|]
          _          -> out1 [qc|({haskellConsName}\{..}, {ofs'})|]

  where
    getExtractorNameWithQuant :: XMLString -> FieldGI -> XMLString -- ? Builder
    getExtractorNameWithQuant ofs fld = do
        let (fieldQuantifier::(Maybe XMLString)) = case fld.cardinality of
                RepMaybe -> Just "extractMaybe"
                RepOnce  -> Nothing
                _        -> Just "extractMany" -- TODO add extractExact support
            fieldTypeName = bld fld.typeName.type_.unHaskellTypeName
        case fieldQuantifier of
                 Nothing   -> [qc|extract{fieldTypeName}Content {ofs}|]
                 Just qntf -> [qc|{qntf} {ofs} extract{fieldTypeName}Content|]

lookupHaskellTypeBySchemaType :: XMLString -> CG TypeWithAttrs
lookupHaskellTypeBySchemaType xmlType = do
  knownTypes_ <- Lens.use knownTypes
  case Map.lookup xmlType knownTypes_ of
    Nothing -> do
      typeDict <- Lens.use schemaTypesMap
      let schemaType =
            fromMaybe (error $ "unknown schema type" <> show xmlType) $
              Map.lookup xmlType typeDict 
      processSchemaNamedType (xmlType, schemaType)
    Just x -> pure x

registerDataDeclaration :: TypeDecl -> CG ()
registerDataDeclaration decl = typeDecls %= (decl :)


registerExtractionFunction :: FunctionBody -> CG ()
registerExtractionFunction fBody = extractFunctions %= (fBody :)

registerParseFunction :: FunctionBody -> CG ()
registerParseFunction fBody = parseFunctions %= (fBody :)

registerSequenceGI :: SequenceGI -> CG ()
registerSequenceGI s = do
  registerDataDeclaration $ Alg $ mkSequenceTypeDeclaration s
  registerParseFunction $ generateSequenceParseFunctionBody s
  registerExtractionFunction $ generateSequenceExtractFunctionBody s

registerAttrContent :: ContentWithAttrsGI -> CG ()
registerAttrContent cgi = do
  registerDataDeclaration $ Alg $ mkAttrContentTypeDeclaration cgi
  registerParseFunction $ generateAttrContentParse cgi
  registerExtractionFunction $ generateAttrContentExtract cgi

registerChoiceGI :: ChoiceGI -> CG ()
registerChoiceGI chGI = do
  registerDataDeclaration $ Sumtype $ mkChoiceTypeDeclaration chGI
  registerParseFunction $ generateChoiceParseFunctionBody chGI
  registerExtractionFunction $ generateChoiceExtractFunctionBody chGI

getAllocatedHaskellTypes :: CG (Set.Set HaskellTypeName)
getAllocatedHaskellTypes = Lens.use allocatedHaskellTypes

getAllocatedHaskellConstructors :: CG (Set.Set HaskellConsName)
getAllocatedHaskellConstructors = Lens.use allocatedHaskellConses

getUniqueName :: (Monad m, Ord a) => (XMLString -> a) -> XMLString -> m (Set.Set a) -> m a
getUniqueName mk possibleName getSet = do
  set_ <- getSet
  pure $ fromJust $ List.find (flip Set.notMember set_) possibleAlternatives
  where
  possibleAlternatives =
    map mk $
      possibleName : map ((possibleName <>) . cs . show) [1..100::Int]

getUniqueTypeName :: XMLString -> CG HaskellTypeName
getUniqueTypeName s = do
  res <- getUniqueName mkHaskellTypeName s getAllocatedHaskellTypes
  allocatedHaskellTypes %= Set.insert res
  pure res

getUniqueConsName :: XMLString -> CG HaskellConsName
getUniqueConsName s = do
  res <- getUniqueName mkHaskellConsName s getAllocatedHaskellConstructors
  allocatedHaskellConses %= Set.insert res
  pure res

processComplex ::
  XMLString -> -- ^ possible name
  Bool ->
  [Attr] ->
  TyPart ->
  CG TypeWithAttrs
processComplex (normalizeTypeName -> possibleName) _mixed attrs inner = case inner of
  Seq seqParts -> case traverse getElement seqParts of
    Nothing -> error "only sequence of elements is supported"
    Just elts -> do
      sGI <- mkSequenceGI elts
      registerSequenceGI sGI
      pure $ TypeWithAttrs sGI.typeName (getSequenceAttrs sGI) $ GSeq sGI
  Choice choiceAlts -> case traverse getElement choiceAlts of
    Nothing -> error "only choice between elements is supported"
    Just elts -> do
      chGI <- mkChoiceGI elts
      registerChoiceGI chGI
      pure $ typeNoAttrs chGI.typeName $ GChoice chGI
  _ -> error "anything other than Seq inside Complex is not supported"
  where
  mkChoiceGI :: [Element] -> CG ChoiceGI
  mkChoiceGI elts = do
    typeName <- getUniqueTypeName possibleName
    alts <- forM elts \el -> do
      altType <- processType (eName el) (eType el)
      consName <- getUniqueConsName $ possibleName <> normalizeTypeName (eName el)
      pure (eName el, consName, altType)
    pure ChoiceGI {typeName, alts}
  mkSequenceGI :: [Element] -> CG SequenceGI
  mkSequenceGI elts = do
    typeName <- getUniqueTypeName possibleName
    consName <- getUniqueConsName possibleName
    attrFields <- mapM attributeToField attrs
    fields <- mapM elementToField elts
    pure SequenceGI
      { typeName
      , consName
      , attributes = attrFields
      , fields
      }
  elementToField :: Element -> CG FieldGI
  elementToField elt = do
    typeName <- processType (eName elt) $ eType elt
    pure FieldGI
      { haskellName = eltNameToHaskellFieldName $ eName elt
      , xmlName = eName elt
      , cardinality = eltToRepeatedness elt
      , typeName
      }
  getElement :: TyPart -> Maybe Element
  getElement (Elt e) = Just e
  getElement _ = Nothing

attributeToField :: Attr -> CG FieldGI
attributeToField attr = do
  typeName <- processType (aName attr) $ aType attr
  pure FieldGI
    { haskellName = attrNameToHaskellFieldName $ aName attr
    , xmlName = aName attr
    , cardinality = RepMaybe
    , typeName
    }

eltNameToHaskellFieldName :: BS.ByteString -> HaskellFieldName
eltNameToHaskellFieldName = HaskellFieldName . normalizeFieldName

attrNameToHaskellFieldName :: XMLString -> HaskellFieldName
attrNameToHaskellFieldName = HaskellFieldName . normalizeFieldName

processType :: XMLString -> Type -> CG TypeWithAttrs
processType (normalizeTypeName -> possibleName) = \case
  Ref knownType ->
    lookupHaskellTypeBySchemaType knownType
  Complex{mixed, attrs, inner} ->
    processComplex possibleName mixed attrs inner
  Restriction{base, restricted} -> case restricted of
    Enum alts -> do
      typeName <- getUniqueTypeName possibleName
      constrs <- forM alts \alt -> (alt,) <$> getUniqueConsName alt
      let
        enum_ = EnumGI {typeName, constrs}
      registerEnumGI enum_
      pure $ typeNoAttrs typeName $ GEnum enum_
    Pattern{} -> processAsNewtype base
    None -> processAsNewtype base
  Extension{base, mixin} -> do
    baseHType <- lookupHaskellTypeBySchemaType base
    (hType, extGI) <- mkExtendedGI mixin possibleName baseHType.type_ baseHType.giType
    registerGI extGI
    pure $ TypeWithAttrs
      { type_ = hType
      , attrs = attrInfoFromGIType extGI
      , giType = extGI
      }
  -- t -> error $ "not ref and complex, not supported: " <> show t
  where
  processAsNewtype base = do
      typeName <- getUniqueTypeName possibleName
      consName <- getUniqueConsName possibleName
      wrappedType <- lookupHaskellTypeBySchemaType base
      let ngi = NewtypeGI {typeName, consName, wrappedType}
      registerNewtypeGI ngi
      pure $ typeNoAttrs typeName $ GWrapper ngi

attrInfoFromGIType :: GIType -> AttributesInfo
attrInfoFromGIType = \case
  GBaseType -> NoAttrs
  GAttrContent cgi -> getExtContentAttrs cgi
  GSeq seq_ -> getSequenceAttrs seq_
  GChoice _ch -> NoAttrs
  GEnum _en -> NoAttrs
  GWrapper _nwt -> NoAttrs

mkExtendedGI :: Type -> XMLString -> HaskellTypeName -> GIType -> CG (HaskellTypeName, GIType)
mkExtendedGI mixin possibleName baseType gi = case gi of
  _x
    | isSimpleContentType gi, Just attrs <- mbAttrsExtension ->
      second GAttrContent <$> addAttrsToSimple attrs
  _ -> error $ "can't extend type " <> show gi <> " and mixin " <> show mixin
  where
  isSimpleContentType = \case
    GBaseType -> True
    GWrapper{} -> True
    GEnum{} -> True
    _ -> False
   
  addAttrsToSimple ::
    NE.NonEmpty Attr ->
    CG (HaskellTypeName, ContentWithAttrsGI)
  addAttrsToSimple attrs = do
    typeName <- getUniqueTypeName possibleName
    consName <- getUniqueConsName possibleName
    attrFields <- mapM attributeToField attrs
    pure $ (typeName,) ContentWithAttrsGI
      { typeName
      , consName
      , attributes = NE.toList attrFields
      , contentType = baseType
      }

  mbAttrsExtension :: Maybe (NE.NonEmpty Attr)
  mbAttrsExtension = case mixin of
    Complex{attrs, inner} -> do
      guard $ inner == Seq []
      NE.nonEmpty attrs
    _ -> Nothing

mkEnumTypeDeclaration :: EnumGI -> (TyData, [Record])
mkEnumTypeDeclaration en =
  (TyData $ B.byteString en.typeName.unHaskellTypeName
  , (\con -> (TyCon $ B.byteString (snd con).unHaskellConsName, [])) <$> en.constrs
  )


mkNewtypeDeclaration :: NewtypeGI -> (TyData, TyCon, TyType)
mkNewtypeDeclaration ngi =
  ( TyData $ B.byteString ngi.typeName.unHaskellTypeName
  , TyCon $ B.byteString ngi.consName.unHaskellConsName
  , TyType $ B.byteString ngi.wrappedType.type_.unHaskellTypeName
  )

generateNewtypeParseFunc :: NewtypeGI -> FunctionBody
generateNewtypeParseFunc ngi = FunctionBody $ runCodeWriter do
  out1 (getParserNameForType ngi.typeName <> " arrStart strStart =")
  withIndent1 do
   out1 [qc|parseString arrStart strStart|]

generateEnumParseFunc :: EnumGI -> FunctionBody
generateEnumParseFunc en = FunctionBody $ runCodeWriter do
  out1 (getParserNameForType en.typeName <> " arrStart strStart =")
  withIndent1 do
   out1 [qc|parseString arrStart strStart|]

generateNewtypeExtractFunc :: NewtypeGI -> FunctionBody
generateNewtypeExtractFunc ngi = FunctionBody $ runCodeWriter do
  let typeName = bld ngi.typeName.unHaskellTypeName
      consName = bld ngi.consName.unHaskellConsName
      wrappedName = bld ngi.wrappedType.type_.unHaskellTypeName
  out1 [qc|extract{typeName}Content ofs =|]
  withIndent1 do
    out1 [qc|first {consName} $ extract{wrappedName}Content ofs|]

generateEnumExtractFunc :: EnumGI -> FunctionBody
generateEnumExtractFunc en = FunctionBody $ runCodeWriter do
  let recType = bld en.typeName.unHaskellTypeName
  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 do
    out1 [qc|first (\case|]
    for_ en.constrs \(xmlName, haskellCon) -> do
      let conBld = bld haskellCon.unHaskellConsName
      out1 [qc|"{bld xmlName}" -> {conBld}|]
    out1 [qc|) $ extractStringContent ofs|]

registerGI :: GIType -> CG ()
registerGI = \case
  GBaseType -> pure ()
  GAttrContent cgi -> registerAttrContent cgi
  GSeq seq_ -> registerSequenceGI seq_
  GChoice ch -> registerChoiceGI ch
  GEnum en -> registerEnumGI en
  GWrapper nwt -> registerNewtypeGI nwt

registerEnumGI :: EnumGI -> CG ()
registerEnumGI e = do
  registerDataDeclaration $ Alg $ mkEnumTypeDeclaration e
  registerExtractionFunction $ generateEnumExtractFunc e
  registerParseFunction $ generateEnumParseFunc e

registerNewtypeGI :: NewtypeGI -> CG ()
registerNewtypeGI ngi = do
  registerDataDeclaration $ Newtype $ mkNewtypeDeclaration ngi
  registerExtractionFunction $ generateNewtypeExtractFunc ngi
  registerParseFunction $ generateNewtypeParseFunc ngi

 

registerNamedType :: XMLString -> TypeWithAttrs -> CG ()
registerNamedType xmlName haskellType = do
  knownTypes %= Map.insert xmlName haskellType
  processedSchemaTypes %= Set.insert xmlName

processSchemaNamedType :: (XMLString, Type) -> CG TypeWithAttrs
processSchemaNamedType (tName, tDef) = do
  q <- Lens.use knownTypes
  case Map.lookup tName q of
    Just q_ -> pure q_
    Nothing -> do
      haskellTypeName <- processType tName tDef
      registerNamedType tName haskellTypeName
      pure haskellTypeName

processSchemaNamedTypes :: TypeDict -> CG ()
processSchemaNamedTypes dict = forM_ (Map.toList dict) processSchemaNamedType

generateModuleHeading ::
  HasCallStack =>
  GenerateOpts ->
  CG ()
generateModuleHeading GenerateOpts{..} = do
    unless isUnsafe $ outCodeLine "{-# LANGUAGE Safe #-}"
    outCodeLine "{-# LANGUAGE DuplicateRecordFields #-}"
    outCodeLine "{-# LANGUAGE BlockArguments  #-}"
    -- TODO add codegen to parser
    outCodeLine "{-# LANGUAGE OverloadedStrings #-}"
    outCodeLine "{-# LANGUAGE RankNTypes #-}"
    outCodeLine "{-# LANGUAGE LambdaCase #-}"
    outCodeLine "{-# LANGUAGE DeriveGeneric #-}"
    outCodeLine "{-# LANGUAGE DeriveAnyClass #-}"
    outCodeLine "{-# LANGUAGE RecordWildCards #-}"
    outCodeLine "{-# LANGUAGE ScopedTypeVariables #-}"
    -- TODO also add in parser generator
    --
    --
    outCodeLine "module XMLSchema where"
    outCodeLine (basePrologue isUnsafe)

identity :: p -> p
identity x = x


