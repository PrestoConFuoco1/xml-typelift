{-# LANGUAGE OverloadedLabels #-}
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
module CodeGen(GenerateOpts(..), parserCodegen, codegen, UseXmlIsogenNaming (..), ShouldGenLenses (..), AllowDuplicatedFields (..)) where

import           Prelude                           hiding (id, lookup)

import Data.String.Conversions
import           Control.Monad
import qualified Data.ByteString.Builder           as B
import qualified Data.ByteString.Char8             as BS
import qualified Data.Map.Strict                   as Map
import           Data.Maybe
import qualified Data.Set                          as Set
import qualified Language.Haskell.TH               as TH
import           Text.InterpolatedString.Perl6     (qc, ShowQ (..))
#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup((<>))
#endif

import           FromXML                           (XMLString, splitNS)

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
import Data.Foldable (for_, asum)
import TypeDecls1 (TypeDecl (..), SumType)
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor (Bifunctor(..))
import Data.Char (isDigit, isUpper, toLower)
import Data.Generics.Labels

--import           Debug.Pretty.Simple
--import           Text.Pretty.Simple
--import           Identifiers

codegen' :: GenerateOpts -> Schema -> CG () -> IO String
codegen' opts sch gen = do
    let output = runCodeGen opts sch gen
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
    codegen' opts sch $ do
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
codegen c sch =
  codegen' c sch $ generateParser2 False c sch

generateParser2 :: Bool -> GenerateOpts -> Schema -> CG ()
generateParser2 genParser opts@GenerateOpts{isGenerateMainFunction, topName} schema = do
    generateModuleHeading opts
    schemaTypesMap .= Map.fromList (map (first mkXmlNameWN) $ Map.toList schema.typesExtended)
    --processSchemaNamedTypes schema.types
    let quals = getSchemaQualNamespace schema
    theSelectedTop <- case topName of
      Nothing -> case schema.tops of
        [] -> error "no toplevel elements"
        [top] -> pure top
        tops_ -> error $ "too much toplevel elements, please specify one of: " <> show (map eName tops_)
      Just userTop -> case List.find (\e -> eName e == cs userTop) schema.tops of
        Nothing -> error $ "toplevel type " <> show userTop <> " not found"
        Just foundUserTop -> pure foundUserTop
    topNameProcessed <- processType quals (Just $ mkXmlNameWN $ eName theSelectedTop) (eType theSelectedTop)
    declaredTypes <- Lens.use typeDecls
    forM_ declaredTypes \case
      Alg rec -> declareAlgebraicType opts rec
      Newtype (t, c, wt) -> declareNewtype t c wt
      Sumtype sumtype -> declareSumType sumtype
    let ShouldGenLenses genLenses = opts.shouldGenerateLenses
    when genLenses $
      forM_ declaredTypes \case
        Alg (TyData tyDataRaw, _) -> outCodeLine [qc|makeLenses ''{tyDataRaw}|]
        Newtype (TyData tyDataRaw, _, _) -> outCodeLine [qc|makePrisms ''{tyDataRaw}|]
        Sumtype (TyData tyDataRaw, _) -> outCodeLine [qc|makePrisms ''{tyDataRaw}|]
    when genParser do
      outCodeLine [qc||]
      outCodeLine [qc|type TopLevel = {type_ topNameProcessed}|]
      outCodeLine [qc|-- PARSER --|]
      generateParserInternalStructures
      generateParserInternalArray1 opts (theSelectedTop, topNameProcessed)
      outCodeLine ""
      outCodeLine ""
      outCodeLine "-- extr --"
      outCodeLine ""
      outCodeLine ""
      generateParserExtractTopLevel1 opts topNameProcessed
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


generateParserInternalArray1 :: GenerateOpts -> (Element, TypeWithAttrs) -> CG ()
generateParserInternalArray1 GenerateOpts{isUnsafe} (topEl, topType) = do
    outCodeLine [qc|-- PARSER --|]
    -- Generate parser header
    let topTag = eName topEl
        topName = unHaskellTypeName $ mkHaskellTypeName topTag
    when (minOccurs topEl /= 1) $ parseErrorBs topName [qc|Wrong minOccurs = {minOccurs topEl}|]
    when (maxOccurs topEl /= MaxOccurs 1) $ parseErrorBs topName [qc|Wrong maxOccurs = {maxOccurs topEl}|]
    let repeatedness = RepOnce
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
                outCodeLine' [qc|let arrOfs0 = 0|]
                outCodeLine' [qc|let strOfs0 = (skipSpaces $ skipHeader $ skipSpaces 0)|]
                let
                  parseElementCall = generateParseElementCall ("arrOfs0", "strOfs0") (Just (topTag, repeatedness)) topType
                outCodeLine' [qc|(_, _) <- {parseElementCall}|]
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
        -- outCodeLine' [qc|getTagName strOfs = BS.takeWhile (\c -> not (isSpaceChar c || c == closeTagChar || c == slashChar)) $ BS.drop (skipToOpenTag strOfs + 1) bs|]
        outCodeLine' [qc|getTagName strOfs = fst $ getTagName' $ (skipToOpenTag strOfs + 1)|]
        outCodeLine' [qc|getTagName' :: Int -> (XMLString, Int)|]
        outCodeLine' [qc|getTagName' strOfs = do|]
        outCodeLine' [qc|  let isAfterTag c = isSpaceChar c || c == closeTagChar || c == slashChar|]
        outCodeLine' [qc|      isQualDelim c = c == colonChar|]
        outCodeLine' [qc|      noColon = BS.takeWhile (\c -> not (isAfterTag c || isQualDelim c)) $ BS.drop strOfs bs|]
        outCodeLine' [qc|      afterNoColonOfs = strOfs + BS.length noColon|]
        outCodeLine' [qc|  if bs `BSU.unsafeIndex` afterNoColonOfs /= colonChar|]
        outCodeLine' [qc|  then (noColon, afterNoColonOfs)|]
        outCodeLine' [qc|  else do|]
        outCodeLine' [qc|    let|]
        outCodeLine' [qc|      afterColon = BS.takeWhile (not . isAfterTag) $ BS.drop (afterNoColonOfs + 1) bs|]
        outCodeLine' [qc|    (afterColon, afterNoColonOfs + 1 + BS.length afterColon)|]
 
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
        -- FIXME: поддержка пустых типов данных
        -- https://stackoverflow.com/questions/7231902/self-closing-tags-in-xml-files
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
        outCodeLine' [qc|            return (arrOfs + 1, strOfs)|]
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
        outCodeLine' [qc|  | expectedTag == actualTagName =|]
        outCodeLine' [qc|      if bs `{bsIndex}` ofsToEnd == closeTagChar|]
        outCodeLine' [qc|        then Just (ofsToEnd + 1, False)|]
        outCodeLine' [qc|      else if isSpaceChar (bs `{bsIndex}` ofsToEnd)|] -- TODO
        outCodeLine' [qc|        then let ofs' = skipToCloseTag (ofs + BS.length expectedTag)|]
        outCodeLine' [qc|             in Just (ofs' + 1, bs `{bsIndex}` (ofs' - 1) == slashChar)|]
        outCodeLine' [qc|      else|]
        outCodeLine' [qc|        Nothing|]
        outCodeLine' [qc|  | otherwise = Nothing|]
        outCodeLine' [qc|  where (actualTagName, ofsToEnd) = getTagName' ofs|]
        outCodeLine' [qc|ensureTag False expectedTag ofs|]
        outCodeLine' [qc|  | expectedTag == actualTagName|]
        outCodeLine' [qc|        = Just (ofsToEnd + 1, False)|]
        outCodeLine' [qc|  | otherwise|]
        outCodeLine' [qc|        = Nothing|]
        outCodeLine' [qc|  where (actualTagName, ofsToEnd) = getTagName' ofs|]
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
        outCodeLine' [qc|  | expectedTag == actualTagName = do|]
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
        outCodeLine' [qc|  where (actualTagName, ofsToEnd) = getTagName' ofs|]


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
        outCodeLine' [qc|  when (arrAttrLocation >= 0) do|]
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
        outCodeLine' [qc|parseGYearMonthContent = parseString|]
        outCodeLine' [qc|parseGYearContent = parseString|]
        outCodeLine' [qc|parseBoolContent = parseString|]
        outCodeLine' [qc|parseGMonthContent = parseString|]
        outCodeLine' [qc|parseIntegerContent = parseString|]
        outCodeLine' [qc|parseIntContent = parseString|]
        -- outCodeLine' [qc|parseUnitContent arrStart strStart = pure (arrStart, strStart)|]
        outCodeLine' [qc|parseUnitContent arrStart strStart =|]
        outCodeLine' [qc|  pure $ (arrStart,) $ parseUnitContentRec (0 :: Int) strStart|]
        outCodeLine' [qc|parseUnitContentRec level strStart = do|]
        outCodeLine' [qc|  let echoNbefore msg n = (msg <> ": " <> show (BS.takeEnd 10 $ BS.take n bs)) `trace` n|]
        outCodeLine' [qc|  let echoWord8 msg x = (msg <> ": " <> show (Data.Char.chr $ fromIntegral x)) `trace` x|]
        outCodeLine' [qc|  let startTagIdx = echo "startTagIdx" $ skipToOpenTag strStart|]
        outCodeLine' [qc|      endTagIdx = echo "endTagIdx" $ skipToCloseTag startTagIdx|]
        outCodeLine' [qc|  if startTagIdx `seq` endTagIdx `seq` (echo "isSlash" (echoWord8 "start+1" (bs `BSU.unsafeIndex` (startTagIdx+1)) == slashChar))|]
        outCodeLine' [qc|    then|]
        outCodeLine' [qc|      -- it's closing tag|]
        outCodeLine' [qc|      (if level == 0 then startTagIdx else parseUnitContentRec (level - 1) endTagIdx)|]
        outCodeLine' [qc|    else if bs `BSU.unsafeIndex` (endTagIdx - 1) == slashChar|]
        outCodeLine' [qc|      -- empty tag, parsing further on the same level|]
        outCodeLine' [qc|      then parseUnitContentRec level endTagIdx|]
        outCodeLine' [qc|      -- open tag, one level deeper|]
        outCodeLine' [qc|      else parseUnitContentRec (level+1) endTagIdx|]

        outCodeLine' [qc|parseInt64Content = parseString|]
        outCodeLine' [qc|parseDayContent = parseString|]
        outCodeLine' [qc|parseTimeOfDayContent = parseString|]
        outCodeLine' [qc|parseZonedTimeContent = parseString|]
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
        outCodeLine' [qc|colonChar = 58 -- '?'|]
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
  TypeWithAttrs ->
  CG ()
generateParserExtractTopLevel1 GenerateOpts{isUnsafe} topType = do
    let topTypeName = topType.type_
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
            outCodeLine' [qc|extractStringContent ofs = (echoN "extractStringContent:result" 15 $ BSU.unsafeTake bslen (BSU.unsafeDrop bsofs bs), ofs + 2)|]
        else
            outCodeLine' [qc|extractStringContent ofs = (BS.take bslen (BS.drop bsofs bs), ofs + 2)|]
        outCodeLine' [qc|  where|]
        outCodeLine' [qc|    bsofs = echo "extractStringContent:offset" $ arr {index} ofs|]
        outCodeLine' [qc|    bslen = echo "extractStringContent:length" $ arr {index} (ofs + 1)|]
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
        outCodeLine' [qc|extractUnitContent ofs = ((), ofs)|]
        outCodeLine' [qc|extractXMLStringContent = extractStringContent|]
        outCodeLine' [qc|extractDateTimeContent :: Int -> (ZonedTime, Int)|]
        outCodeLine' [qc|extractDateTimeContent = extractAndParse zonedTimeStr|]
        let
          typesUsingReadInstance = 
            ["Day", "GYear", "Scientific", "Integer", "Int", "Int64"] :: [String]
          typesUsingCustomParsers :: [(String, String)] =
            [ ("GYearMonth", "(readStringMaybe $ parseTimeM True defaultTimeLocale \"%Y-%-m\")")
            , ("GMonth", "(readStringMaybe parseGMonth)")
            , ("TimeOfDay", "(readStringMaybe iso8601ParseM)")
            , ("ZonedTime", "(readStringMaybe iso8601ParseM)")
            , ("Duration", "parseDuration")
            ]
          mkParseRawTypeSig :: String -> String
          mkParseRawTypeSig t = [qc|parse{t}Raw :: ByteString -> Either String {t}|]
          readInstanceParseRawBody :: String -> String
          readInstanceParseRawBody t = [qc|parse{t}Raw = readEither|]
          mkCustomParseRawBody :: String -> String -> String
          mkCustomParseRawBody t parse_ = [qc|parse{t}Raw = {parse_}|]
        for_ typesUsingReadInstance \t -> do
          outCodeLine' $ mkParseRawTypeSig t
          outCodeLine' $ readInstanceParseRawBody t
        for_ typesUsingCustomParsers \(t, p) -> do
          outCodeLine' $ mkParseRawTypeSig t
          outCodeLine' $ mkCustomParseRawBody t p
        for_ ("Bool" : typesUsingReadInstance <> map fst typesUsingCustomParsers) \t -> do
          outCodeLine' [qc|extract{t}Content :: Int -> ({t}, Int)|]
          outCodeLine' [qc|extract{t}Content = extractAndParse parse{t}Raw|]
        outCodeLine' [qc|parseXMLStringRaw :: ByteString -> Either String ByteString|]
        outCodeLine' [qc|parseXMLStringRaw = pure|]

        outCodeLine' [qc|parseBoolRaw = \case|]
        outCodeLine' [qc|    "true" -> Right True|]
        outCodeLine' [qc|    "1" -> Right True|]
        outCodeLine' [qc|    "false"-> Right False|]
        outCodeLine' [qc|    "0" -> Right False|]
        outCodeLine' [qc|    unexp -> Left $ "unexpected bool value: " <> show unexp|]
        outCodeLine' [qc|first f (a,b) = (f a, b)|]
        outCodeLine' [qc|extractAndParse :: (ByteString -> Either String a) -> Int -> (a, Int)|]
        outCodeLine' [qc|extractAndParse parser ofs = first (catchErr ofs parser) $ extractStringContent ofs|]

        outCodeLine' [qc|catchErr :: Int -> (ByteString -> Either String b) -> ByteString -> b|]
        outCodeLine' [qc|catchErr ofs f str = either (\msg -> parseError bsofs bs msg) id (f str)|]
        outCodeLine' [qc|  where bsofs = arr {index} ofs|]
        outCodeLine' [qc|readEither :: Read a => ByteString -> Either String a|]
        outCodeLine' [qc|readEither str =|]
        outCodeLine' [qc|    case reads (BSC.unpack str) of|]
        outCodeLine' [qc|        [(a, [])] -> Right a|]
        outCodeLine' [qc|        _ -> Left $ "Can't parse " ++ show str|]
        outCodeLine' [qc|readStringMaybe :: (String -> Maybe a) -> ByteString -> Either String a|]
        outCodeLine' [qc|readStringMaybe strParser input =|]
        outCodeLine' [qc|  case strParser (BSC.unpack input) of|]
        outCodeLine' [qc|    Just res -> pure res|]
        outCodeLine' [qc|    Nothing -> Left $ "Can't parse " ++ show input|]
        outCodeLine' [qc|fst3 (x, _, _) = x|]
        outCodeLine' [qc|snd3 (_, y, _) = y|]
        outCodeLine' [qc|thrd3 (_, _, z) = z|]
        outCodeLine' [qc|dayYear = fst3 . toGregorian|]
        outCodeLine' [qc|dayMonthOfYear = snd3 . toGregorian|]
        outCodeLine' [qc|parseGMonth str =|]
        outCodeLine' [qc|  let stripped = dropWhile Data.Char.isSpace str in|]
        outCodeLine' [qc|  if "--" `isPrefixOf` stripped|]
        outCodeLine' [qc|  then fmap dayMonthOfYear $ parseTimeM True defaultTimeLocale "%-m" $ drop 2 stripped|]
        outCodeLine' [qc|  else Nothing|]


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

{-
    outCodeLine' [qc|echo = \_ -> id|]
    outCodeLine' [qc|echoN = \_ _ -> id|]
-}
    outCodeLine' [qc|echo :: Show a => String -> a -> a|]
    outCodeLine' [qc|echo msg x = (msg <> ": " <> show x) `trace` x|]
    outCodeLine' ""
    outCodeLine' [qc|echoN :: Show a => String -> Int -> a -> a|]
    outCodeLine' [qc|echoN msg n x = (msg <> ": " <> take n (show x)) `trace` x|]

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
  ( TyData $ B.byteString ch.typeName.unHaskellTypeName
  , flip map ch.alts \(inTagInfo, _possibleTags, cons_, conType) ->
    ( TyCon $ B.byteString cons_.unHaskellConsName
    , TyType $ mkTypeWithCardinality inTagInfo $ B.byteString conType.type_.unHaskellTypeName
    )
  )

mkSequenceTypeDeclaration :: SequenceGI -> (TyData, [Record])
mkSequenceTypeDeclaration s =
  (TyData $ B.byteString s.typeName.unHaskellTypeName
  , [ ( TyCon $ B.byteString s.consName.unHaskellConsName
      , map mkAttrFieldDeclaration s.attributes <> map mkFieldDeclaration s.fields
      )
    ]
  )

mkAttrContentTypeDeclaration :: ContentWithAttrsGI -> (TyData, [Record])
mkAttrContentTypeDeclaration cgi =
  ( TyData $ B.byteString cgi.typeName.unHaskellTypeName
  , [ ( TyCon $ B.byteString cgi.consName.unHaskellConsName
      , map mkAttrFieldDeclaration cgi.attributes <> map mkFieldDeclaration [cgi.content]
      )
    ]
  )
  {-
  where
  contentField :: FieldGI
  contentField =
    -- TODO: maybe it's not the best idea to use FieldGI here
    FieldGI
      { haskellName = cgi.contentFieldName
      , typeName = typeNoAttrs cgi.contentType GBaseType
      , inTagInfo = Nothing
      }
-}

mkFieldDeclaration :: FieldGI -> TyField
mkFieldDeclaration fld =
  ( TyFieldName $ B.byteString fld.haskellName.unHaskellFieldName
  , TyType $ mkTypeWithCardinality fld.inTagInfo $ B.byteString fld.typeName.type_.unHaskellTypeName
  )

mkTypeWithCardinality :: Maybe (a1, Repeatedness) -> B.Builder -> B.Builder
mkTypeWithCardinality inTagInfo x = case inTagInfo of
  Nothing -> x
  Just (_, card) -> case card of
    RepMaybe -> "Maybe " <> x
    RepOnce -> x
    _ -> "[" <> x <> "]"

mkAttrFieldDeclaration :: AttrFieldGI -> TyField
mkAttrFieldDeclaration fld =
  ( TyFieldName $ B.byteString fld.haskellName.unHaskellFieldName
  , TyType $ typeWithUse $ B.byteString fld.typeName.type_.unHaskellTypeName
  )
  where
  attrRequired = fld.attrUse == Required
  typeWithUse x =
    if attrRequired
    then x
    else "Maybe " <> x

{-
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
-}

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

generateAttrContentParse :: ContentWithAttrsGI -> FunctionBody
generateAttrContentParse cgi = FunctionBody $ runCodeWriter do
  generateAttrsAllocation
    TypeWithAttrs {type_ = cgi.typeName, giType = GAttrContent cgi}
  out1 (getParserNameForType cgi.typeName <> " = " <> getParserNameForType cgi.content.typeName.type_)

generateSequenceParseFunctionBody :: SequenceGI -> FunctionBody
generateSequenceParseFunctionBody s = FunctionBody $ runCodeWriter do
  generateAttrsAllocation
    TypeWithAttrs { type_ = s.typeName, giType = GSeq s }
  out1 (getParserNameForType s.typeName <> " arrStart strStart = do")
  withIndent1 do
    let (arrStart, strStart) = ("arrStart", "strStart")
        fields = {- s.attributes <> -} s.fields
    let ofsNames' = ((arrStart, strStart) : [ ( [qc|arrOfs{i}|], [qc|strOfs{i}|]) | i <- [(1::Int)..]])
                    :: [(XMLString, XMLString)]
        ofsNames = zip ofsNames' (tail ofsNames')
        (arrRet, strRet) = ofsNames' !! length fields
    forM_ (zip ofsNames fields) $ \((oldOffsets, (arrOfs', strOfs')), field) -> do
      out1 [qc|({arrOfs'}, {strOfs'}) <- do|]
      withIndent1 do
        -- offsetsAfterAllocGen <- generateAttrsAllocation oldOffsets field.typeName
        out1 $ generateParseElementCall oldOffsets field.inTagInfo field.typeName
    out1 [qc|pure ({arrRet}, {strRet})|]

generateAttrsAllocation ::
  TypeWithAttrs ->
  CodeWriter
generateAttrsAllocation TypeWithAttrs{type_, giType} =
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
  withPresentAttrs action = case attrInfoFromGIType giType of
    NoAttrs -> pure ()
    AttributesInfo neStr -> action neStr

generateParseElementCall ::
  (XMLString, XMLString) ->
  Maybe (XMLString, Repeatedness) ->
  TypeWithAttrs ->
  String
generateParseElementCall (arrOfs, strOfs) inTagInfo typeWithAttrs = do
  let parsedType = typeWithAttrs.type_
      parserName = getParserNameForType parsedType
      hasAttrs = attrInfoFromGIType typeWithAttrs.giType /= NoAttrs
      (allocator :: B.Builder, tagQModifier) =
        if hasAttrs
        then ([qc|{getAttrsAllocatorName parsedType} {getAttrsRoutingName parsedType} |], (<> ("WithAttrs" :: String)))
        else ("", identity)
  let mbTagAndQuantifier = case inTagInfo of
        Nothing -> Nothing
        Just (tagName_, card) -> Just . (tagName_,) $ case card of
          RepMaybe -> "inMaybeTag"
          RepOnce  -> "inOneTag"
          _        -> "inManyTags"
  case mbTagAndQuantifier of
    Nothing -> [qc|{parserName} {arrOfs} {strOfs}|]
    Just (tagName, tagQuantifier) -> 
      [qc|{tagQModifier tagQuantifier} {allocator}"{tagName}" {arrOfs} {strOfs} {parserName}|]

getAttrsRoutingName :: HaskellTypeName -> XMLString
getAttrsRoutingName t = [qc|get{t}AttrOffset|]

getAttrsAllocatorName :: HaskellTypeName -> XMLString
getAttrsAllocatorName t = [qc|allocate{t}Attrs|]

generateChoiceParseFunctionBody :: ChoiceGI -> FunctionBody
generateChoiceParseFunctionBody ch = FunctionBody $ runCodeWriter $
  out1 (getParserNameForType ch.typeName <> " arrStart strStart = do") >> withIndent1 do
    out1 [qc|let tagName = getTagName strStart|]
    out1 [qc|case tagName of|]
    withIndent1 $ forM_ (zip ch.alts [0 :: Int ..]) \((inTagInfo, possibleFirstTags, _cons, type_), altIdx) -> do
      let vecWrite {- | isUnsafe -} = "V.unsafeWrite" :: B.Builder
          captureCon = [qc|{vecWrite} vec arrStart {altIdx}|] :: B.Builder
          parseFunc1 =
            generateParseElementCall ("(arrStart + 1)", "strStart") inTagInfo type_
      forM_ possibleFirstTags \firstTag ->
        out1 [qc|"{firstTag}" -> {captureCon} >> {parseFunc1}|]

generateChoiceExtractFunctionBody :: ChoiceGI -> FunctionBody
generateChoiceExtractFunctionBody ch = FunctionBody $ runCodeWriter do
  let chName = ch.typeName
  out1 [qc|extract{chName}Content ofs = do|]
  withIndent1 do
    let vecIndex = "`V.unsafeIndex`" :: String
    out1 [qc|let altIdx = arr {vecIndex} ofs|]
    out1 [qc|case altIdx of|]
    withIndent1 $ forM_ (zip ch.alts [0 :: Int ..]) \((inTagInfo, _possibleFirstTags, cons_, type_), altIdx) -> do
      let typeName = type_.type_
      -- out1 [qc|{altIdx} -> first {cons_} $ extract{typeName}Content (ofs + 1)|]
      let extractor = getExtractorNameWithQuant "(ofs + 1)" inTagInfo typeName
      out1 [qc|{altIdx} -> first {cons_} $ {extractor}|]

generateAttrContentExtract :: ContentWithAttrsGI -> FunctionBody
generateAttrContentExtract cgi = FunctionBody $ runCodeWriter do
  let recType = cgi.typeName
  let baseType = cgi.content.typeName.type_
  let contentField = cgi.content.haskellName
  let attrNum = length cgi.attributes
  let consName = cgi.consName
  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 $ do
    forM_ (zip cgi.attributes [1..attrNum]) $ \(attr, aIdx) -> do
        let oldOfs = if aIdx == 1 then "ofs" :: XMLString else [qc|ofs{aIdx-1}|]
        let haskellAttrName = attr.haskellName.unHaskellFieldName
        let haskellTypeName = attr.typeName.type_
        let
          attrRequired = case attr.attrUse of
            Required -> True
            _ -> False
        let
          requiredModifier =
            if attrRequired
            then [qc|first (fromMaybe $ error $ "attribute {haskellAttrName} in type {recType} is required but it's absent") $ |]
            else "" :: String

        out1 [qc|let ({haskellAttrName}, ofs{aIdx}) = {requiredModifier}extractAttribute {oldOfs} extract{haskellTypeName}Content in|]
    out1 [qc|let ({contentField}, ofs{attrNum + 1}) = extract{baseType}Content ofs{attrNum} in|]
    out1 [qc|({consName}\{..}, ofs{attrNum + 1})|]

generateSequenceExtractFunctionBody :: SequenceGI -> FunctionBody
generateSequenceExtractFunctionBody s = FunctionBody $ runCodeWriter do
  let recType = s.typeName
  let attrNum = length s.attributes
  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 $ do
      attrFields <- forM (zip s.attributes [1..attrNum]) $ \(attr, aIdx) -> do
          let oldOfs = if aIdx == 1 then "ofs" :: XMLString else [qc|ofs{aIdx-1}|]
          let haskellAttrName = attr.haskellName
          let haskellTypeName = attr.typeName.type_
          let
            attrRequired = attr.attrUse == Required
          let
            requiredModifier =
              if attrRequired
              then [qc|first (fromMaybe $ error $ "attribute {haskellAttrName} in type {recType} is required but it's absent") $ |]
              else "" :: String
          out1 [qc|let ({haskellAttrName}, ofs{aIdx}) = {requiredModifier}extractAttribute {oldOfs} extract{haskellTypeName}Content in|]
          return haskellAttrName
      properFields <- forM (zip s.fields [(attrNum + 1)..]) $ \(fld, ofsIdx::Int) -> do
              let ofs = if ofsIdx == 1 then ("ofs"::XMLString) else [qc|ofs{ofsIdx - 1}|]
                  fieldName = fld.haskellName
                  extractor = getExtractorNameWithQuant ofs fld.inTagInfo fld.typeName.type_
              out1 [qc|let ({fieldName}, ofs{ofsIdx}) = {extractor} in|]
              return fieldName
      let fields = attrFields ++ properFields
          ofs' = if null fields then "ofs" else [qc|ofs{length fields}|]::XMLString
          haskellConsName = s.consName
      case fields of
          []         -> out1 [qc|({haskellConsName}, {ofs'})|]
          [oneField] -> out1 [qc|({haskellConsName} {oneField}, {ofs'})|]
          _          -> out1 [qc|({haskellConsName}\{..}, {ofs'})|]

getExtractorNameWithQuant :: XMLString -> Maybe (XMLString, Repeatedness) -> HaskellTypeName -> XMLString -- ? Builder
getExtractorNameWithQuant ofs inTagInfo fieldTypeName = do
    let (fieldQuantifier::(Maybe XMLString)) = case inTagInfo of
          Nothing -> Nothing
          Just (_, card) -> case card of
            RepMaybe -> Just "extractMaybe"
            RepOnce  -> Nothing
            _        -> Just "extractMany" -- TODO add extractExact support
    case fieldQuantifier of
             Nothing   -> [qc|extract{fieldTypeName}Content {ofs}|]
             Just qntf -> [qc|{qntf} {ofs} extract{fieldTypeName}Content|]

lookupSchemaType :: QualNamespace -> XMLString -> CG (Namespace, (Type, QualNamespace))
lookupSchemaType quals xmlType = do
  schemaTypes <- Lens.use schemaTypesMap
  let (namespaceShort, XmlNameWN -> typeName) = splitNS xmlType
  let typesWithName =
        withTypeNotFoundErr $
          Map.lookup typeName schemaTypes
  let mbNamespace = do
        guard $ not $ BS.null namespaceShort
        Map.lookup (Qual namespaceShort) quals

  pure case mbNamespace of
    Nothing -> do
      let typeWithoutSchema = List.find ((== Namespace "") . fst) typesWithName
      let singleType = guard (length typesWithName == 1) >> Just (head typesWithName)
      withTypeNotFoundErr $ asum [typeWithoutSchema, singleType]
    Just namespace_ -> do
      withTypeNotFoundErr $ List.find ((== namespace_) . fst) typesWithName
  where
  withTypeNotFoundErr :: Maybe c -> c
  withTypeNotFoundErr =
    fromMaybe $ error $ "type not found: " <> cs xmlType


lookupHaskellTypeBySchemaType :: QualNamespace -> XMLString -> CG TypeWithAttrs
lookupHaskellTypeBySchemaType quals xmlType =
 let (namespaceShort, XmlNameWN -> typeName) = splitNS xmlType in
 case Map.lookup typeName knownBaseTypes of
 Just x -> pure x
 Nothing -> do
  knownTypes_ <- Lens.use knownTypes
  schemaTypes <- Lens.use schemaTypesMap
  let withTypeNotFoundErr :: Maybe c -> c
      withTypeNotFoundErr = withTypeNotFoundErr' knownTypes_ schemaTypes
  let mbNamespace = do
        guard $ not $ BS.null namespaceShort
        Map.lookup (Qual namespaceShort) quals
  let
    (namespace, (knownSchType, quals_)) = do
      let typesWithName =
            withTypeNotFoundErr $
              Map.lookup typeName schemaTypes
      case mbNamespace of
        Nothing -> do
          let typeWithoutSchema = List.find ((== Namespace "") . fst) typesWithName
          let singleType = guard (length typesWithName == 1) >> Just (head typesWithName)
          withTypeNotFoundErr $ asum [typeWithoutSchema, singleType]
        Just namespace_ -> do
          withTypeNotFoundErr $ List.find ((== namespace_) . fst) typesWithName

  case Map.lookup typeName knownTypes_ of
    Nothing -> processSchemaNamedType quals_ namespace (mkXmlNameWN $ xmlType, knownSchType)
    Just hTypesWithNamespaces ->
      case List.lookup namespace hTypesWithNamespaces of
        Nothing -> processSchemaNamedType quals_ namespace (mkXmlNameWN $ xmlType, knownSchType)
        Just x -> pure x
  where
  
  withTypeNotFoundErr' :: (Show a, Show b) => a -> b -> Maybe c -> c
  withTypeNotFoundErr' knownTypes_ schemaTypes =
    fromMaybe $ error $ "type not found: " <> cs xmlType <>
      "\n known haskell types: " <> show knownTypes_ <>
      "\n known schema types: " <> show schemaTypes

registerDataDeclaration :: TypeDecl -> CG ()
registerDataDeclaration decl = typeDecls %= (decl :)

registerExtractionFunction :: FunctionBody -> CG ()
registerExtractionFunction fBody = extractFunctions %= (fBody :)

registerParseFunction :: FunctionBody -> CG ()
registerParseFunction fBody = parseFunctions %= (fBody :)

registerSequenceGI :: SequenceGI -> CG ()
registerSequenceGI s = do
  newAttrs <- forM s.attributes (getAttrFieldName s.typeName)
  newFields <- forM s.fields (finalizeFieldName s.typeName)
  let
    attrsFin = s
      & #attributes .~ newAttrs
      & #fields .~ newFields
  registerDataDeclaration $ Alg $ mkSequenceTypeDeclaration attrsFin
  registerParseFunction $ generateSequenceParseFunctionBody attrsFin
  registerExtractionFunction $ generateSequenceExtractFunctionBody attrsFin

registerAttrContent :: ContentWithAttrsGI -> CG ()
registerAttrContent cgi = do
  newAttrs <- forM cgi.attributes (getAttrFieldName cgi.typeName)
  newContent <- finalizeFieldName cgi.typeName cgi.content
  let
    attrsFin =
      cgi
        & #attributes .~ newAttrs
        & #content .~ newContent
  registerDataDeclaration $ Alg $ mkAttrContentTypeDeclaration attrsFin
  registerParseFunction $ generateAttrContentParse attrsFin
  registerExtractionFunction $ generateAttrContentExtract attrsFin

registerChoiceGI :: ChoiceGI -> CG ()
registerChoiceGI chGI = do
  registerDataDeclaration $ Sumtype $ mkChoiceTypeDeclaration chGI
  registerParseFunction $ generateChoiceParseFunctionBody chGI
  registerExtractionFunction $ generateChoiceExtractFunctionBody chGI

getAllocatedHaskellTypes :: CG (Set.Set HaskellTypeName)
getAllocatedHaskellTypes = Lens.use allocatedHaskellTypes

getAllocatedHaskellConstructors :: CG (Set.Set HaskellConsName)
getAllocatedHaskellConstructors = Lens.use allocatedHaskellConses

echo :: Show a => String -> a -> a
echo msg x = (msg <> ": " <> show x) `trace` x

getUniqueName :: (Monad m, Ord a) => (XMLString -> a) -> XMLString -> m (Set.Set a) -> m a
getUniqueName mk possibleName getSet = do
  set_ <- getSet
  pure $ fromJust $ List.find (flip Set.notMember set_) possibleAlternatives
  where
  possibleAlternatives =
    map mk $
      possibleName : map ((possibleName <>) . cs . show) [1..100::Int]

append'Xml' :: GenerateOpts -> XMLString -> XMLString
append'Xml' opts x =
      if isogenNaming
      then "Xml" <> normalizeTypeName x
      else x
  where
  UseXmlIsogenNaming isogenNaming = opts.useXmlIsogenNaming

{-
wordChar :: Word8 -> Char
wordChar w = chr $ fromIntegral w

charWord :: Char -> Word8
charWord = fromIntegral . ord
-}

getMainLetters :: XMLString -> XMLString
getMainLetters = BS.map toLower . BS.filter (\c -> isDigit c || isUpper c)

appendMainLetters :: GenerateOpts -> HaskellTypeName -> XMLString -> XMLString
appendMainLetters opts typeName x =
  if isogenNaming
  then do
    getMainLetters typeName.unHaskellTypeName <> norm
  else typeName.unHaskellTypeName <> norm
  where
  norm = normalizeTypeName x
  UseXmlIsogenNaming isogenNaming = opts.useXmlIsogenNaming

appendTypeName :: GenerateOpts -> HaskellTypeName -> XMLString -> XMLString
appendTypeName opts typeName x =
  if isogenNaming
  then typeName.unHaskellTypeName <> normalizeTypeName x
  else x
  where
  UseXmlIsogenNaming isogenNaming = opts.useXmlIsogenNaming

getUniqueTypeName :: XMLString -> CG HaskellTypeName
getUniqueTypeName raw = do
  genOpts <- asks genOpts
  let
    getRaw' =
      mkHaskellTypeName . append'Xml' genOpts
  res <- getUniqueName getRaw' raw getAllocatedHaskellTypes
  allocatedHaskellTypes %= Set.insert res
  pure res

getUniqueFieldName :: XMLString -> CG HaskellFieldName
getUniqueFieldName raw = do
  res <- getUniqueName HaskellFieldName raw (Lens.use allocatedFieldNames)
  allocatedFieldNames %= Set.insert res
  pure res

mkFieldName ::
  GenerateOpts ->
  HaskellTypeName ->
  XMLString ->
  CG HaskellFieldName
mkFieldName opts typeName x = do
  let AllowDuplicatedFields allowDup = opts.allowDuplicatedFields
  if allowDup
    then pure $ HaskellFieldName possibleName
    else getUniqueFieldName possibleName
  where
  possibleName =
    (lensesPrefix <>) $
    if isogenNaming
      then getMainLetters typeName.unHaskellTypeName <> hackDropUnderscores (normalizeTypeName x)
      else normalizeTypeName x

  UseXmlIsogenNaming isogenNaming = opts.useXmlIsogenNaming
  ShouldGenLenses genLenses = opts.shouldGenerateLenses
  lensesPrefix = if genLenses then "_" else ""
  hackDropUnderscores = BS.dropWhile (== '_')

data ConsNameOption
  = CnoRecord
  | CnoSum HaskellTypeName
  | CnoEnum HaskellTypeName

getUniqueConsName :: ConsNameOption -> XMLString -> CG HaskellConsName
getUniqueConsName cno s = do
  genOpts <- asks genOpts
  let
    modifierFunc = mkHaskellConsName . case cno of
      CnoRecord -> append'Xml' genOpts
      CnoSum typeName -> appendMainLetters genOpts typeName
      CnoEnum typeName -> appendTypeName genOpts typeName
  res <- getUniqueName modifierFunc s getAllocatedHaskellConstructors
  allocatedHaskellConses %= Set.insert res
  pure res

-- TODO: process attribute groups in more natural way
processAttrGroup ::
  Maybe XmlNameWN ->
  QualNamespace ->
  [Attr] ->
  CG TypeWithAttrs
processAttrGroup nm quals attrs = do
  attrFields <- concat <$> mapM (attributeToField "" quals) attrs
  let
    q =
      GSeq SequenceGI
        { typeName = error "typeName should not be used"
        , consName = error "consName should not be used"
        , attributes = attrFields
        , fields = []
        }
  pure $
    -- TyPartInfo
    TypeWithAttrs (error $ "partType should not be used; attrs: " <> show attrs <> "; name=" <> show nm) q
    -- , inTagInfo = error "inTagInfo should not be used"
    -- , possibleFirstTag = error "possibleFirstTag should not be used"
    -- }

processSeq ::
  Maybe XmlNameWN ->
  QualNamespace ->
  [Attr] ->
  [TyPart] ->
  CG TyPartInfo
processSeq mbPossibleName quals attrs seqParts = do
  underTypes <- forM seqParts (processTyPart Nothing quals False [])
  let
    possibleName =
      fromMaybe "UnknownSeq" $
        asum
          [ unXmlNameWN <$> mbPossibleName
          , (<> "Etc") . unHaskellTypeName . (.partType.type_) <$> listToMaybe underTypes
          ]
  seqGI <- mkSequenceGI possibleName underTypes
  registerSequenceGI seqGI
  let
    type_ = TypeWithAttrs
      { type_ = seqGI.typeName
      , giType = GSeq seqGI
      }
  pure TyPartInfo
    { partType = type_
    , inTagInfo = Nothing
    , possibleFirstTag = (head underTypes).possibleFirstTag
    }
  where
  mkSequenceGI :: XMLString -> [TyPartInfo] -> CG SequenceGI
  mkSequenceGI possibleName tyParts = do
    typeName <- getUniqueTypeName possibleName
    consName <- getUniqueConsName CnoRecord possibleName
    attrFields <- concat <$> mapM (attributeToField typeName quals) attrs
    fields <- mapM elementToField tyParts
    pure SequenceGI
      { typeName
      , consName
      , attributes = attrFields
      , fields
      }
  elementToField :: TyPartInfo -> CG FieldGI
  elementToField tyPart = do
    pure FieldGI
      { haskellName = case tyPart.inTagInfo of
        Nothing -> HaskellFieldName tyPart.partType.type_.unHaskellTypeName
        Just (tagName, _) -> HaskellFieldName tagName
      , typeName = tyPart.partType
      , inTagInfo = tyPart.inTagInfo
      }

processChoice ::
  Maybe XmlNameWN ->
  QualNamespace ->
  [TyPart] ->
  CG TyPartInfo
processChoice mbPossibleName quals choiceAlts = do
  underTypes <- forM choiceAlts (processTyPart Nothing quals False [])
  let
    possibleName =
      fromMaybe "UnknownChoice" $
        asum
          [ unXmlNameWN <$> mbPossibleName
          , (<> "Or'") . unHaskellTypeName . (.partType.type_) <$> listToMaybe underTypes
          ]
  chGI <- mkChoiceGI possibleName underTypes
  registerChoiceGI chGI
  let
    type_ = TypeWithAttrs
      { type_ = chGI.typeName
      , giType = GChoice chGI
      }
  pure TyPartInfo
    { partType = type_
    , inTagInfo = Nothing
    , possibleFirstTag = concatMap possibleFirstTag underTypes
    }
  where
  mkChoiceGI :: XMLString -> [TyPartInfo] -> CG ChoiceGI
  mkChoiceGI possibleName tyParts = do
    typeName <- getUniqueTypeName possibleName
    alts <- forM tyParts \tp -> do
      let
        altConsRaw =
            normalizeTypeName (maybe tp.partType.type_.unHaskellTypeName fst tp.inTagInfo)
      consName <- getUniqueConsName (CnoSum typeName) altConsRaw
      pure (tp.inTagInfo, tp.possibleFirstTag, consName, tp.partType)
    pure ChoiceGI {typeName, alts}

data TyPartInfo = TyPartInfo
  { partType :: TypeWithAttrs
  , inTagInfo :: Maybe (XMLString, Repeatedness)
  , possibleFirstTag :: [XMLString]
  }

processTyPart ::
  Maybe XmlNameWN -> -- ^ possible name
  QualNamespace ->
  Bool ->
  [Attr] ->
  TyPart ->
  CG TyPartInfo
processTyPart possibleName quals _mixed attrs inner = case inner of
  Seq seqParts -> processSeq possibleName quals attrs seqParts
  Choice choiceAlts -> processChoice possibleName quals choiceAlts
  Elt elt -> do
    eltType <- processType quals (Just $ mkXmlNameWN $ eName elt) (eType elt)
    pure TyPartInfo
      { partType = eltType
      , inTagInfo = Just (eName elt, eltToRepeatedness elt)
      , possibleFirstTag = [eName elt]
      }
  unexp -> error $ "anything other than Seq or Choice inside Complex is not supported: " <> show unexp

getAttrFieldName :: HaskellTypeName -> AttrFieldGI -> CG AttrFieldGI
getAttrFieldName headTypeName agi = do
  genOpts <- asks genOpts
  newFieldName <- mkFieldName genOpts headTypeName agi.xmlName
  pure (agi
    { haskellName = newFieldName
    } :: AttrFieldGI)

finalizeFieldName :: HaskellTypeName -> FieldGI -> CG FieldGI
finalizeFieldName headTypeName fgi = do
  genOpts <- asks genOpts
  newFieldName <- mkFieldName genOpts headTypeName fgi.haskellName.unHaskellFieldName
  pure (fgi
    { haskellName = newFieldName
    } :: FieldGI)

attributeToField :: HaskellTypeName -> QualNamespace -> Attr -> CG [AttrFieldGI]
attributeToField headTypeName quals attr = case attr of
  AttrGrp AttrGroupRef{ref} -> do
    TypeWithAttrs{giType} <- lookupHaskellTypeBySchemaType quals ref
    let
      modifyFieldName :: AttrFieldGI -> AttrFieldGI
      modifyFieldName field =
        AttrFieldGI
          { haskellName = error "should not be used before finalizing"
          , xmlName = field.xmlName
          , typeName = field.typeName
          , attrUse = field.attrUse
          }
    case giType of
      GSeq seq_ | null seq_.fields ->
        pure $ map modifyFieldName seq_.attributes
      _ -> error "expected attribute group"
  Attr{aType, use = echo "use" -> use_} -> do
    typeName <- processType quals (Just $ mkXmlNameWN $ aName attr) aType
    pure $ List.singleton AttrFieldGI
      { haskellName = error "single attr: should not be used before finalizing"
      , xmlName = aName attr
      , typeName
      , attrUse = use_
      }

processType :: QualNamespace -> Maybe XmlNameWN -> Type -> CG TypeWithAttrs
processType quals mbPossibleName = \case
  Ref knownType ->
    lookupHaskellTypeBySchemaType quals knownType
  Complex{mixed, attrs, inner} ->
    partType <$> processTyPart mbPossibleName quals mixed attrs inner
  AttrGroupType attrs -> processAttrGroup mbPossibleName quals attrs
  Restriction{base, restricted} -> case restricted of
    Enum alts -> do
      let possibleName = fromMaybe (error "anonymous enums are not supported") mbPossibleName
      typeName <- getUniqueTypeName possibleName.unXmlNameWN
      constrs <- forM alts \alt -> (alt,) <$> getUniqueConsName (CnoEnum typeName) alt
      let
        enum_ = EnumGI {typeName, constrs}
      registerEnumGI enum_
      pure $ typeNoAttrs typeName $ GEnum enum_
    Pattern{} -> processAsNewtype base
    None -> processAsNewtype base
  Extension{base, mixin} -> do
    baseHType <- lookupHaskellTypeBySchemaType quals base
    let possibleName = fromMaybe (XmlNameWN $ baseHType.type_.unHaskellTypeName <> "Ext") mbPossibleName
    ((hType, extGI), shouldRegister) <- mkExtendedGI quals mixin possibleName baseHType.type_ baseHType.giType
    when shouldRegister $ registerGI extGI
    pure $ TypeWithAttrs
      { type_ = hType
      , giType = extGI
      }
  ListType{itemTypeRef} -> do
    itemType <- lookupHaskellTypeBySchemaType quals itemTypeRef
    let possibleName = fromMaybe (XmlNameWN $ itemType.type_.unHaskellTypeName <> "List") mbPossibleName
    typeName <- getUniqueTypeName possibleName.unXmlNameWN
    consName <- getUniqueConsName CnoRecord possibleName.unXmlNameWN
    let listGI = ListGI {typeName, consName, itemType = itemType.type_}
    registerListGI listGI
    pure $ TypeWithAttrs typeName $ GList listGI
  where
  processAsNewtype base = do
      let
        possibleName =
          fromMaybe (mkXmlNameWN $ base <> "Wrapper") mbPossibleName
      typeName <- getUniqueTypeName possibleName.unXmlNameWN
      consName <- getUniqueConsName CnoRecord possibleName.unXmlNameWN
      wrappedType <- lookupHaskellTypeBySchemaType quals base
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
  GList {} -> NoAttrs

mkExtendedGI ::
  QualNamespace ->
  Type ->
  XmlNameWN ->
  HaskellTypeName ->
  GIType ->
  CG ((HaskellTypeName, GIType), Bool {- should we register resulting type -} )
mkExtendedGI quals mixin possibleName baseType gi = case gi of
  _x
    | isEmptyExtension -> do
      pure ((baseType, gi), False)
    | isSimpleContentType gi, Just attrs <- mbAttrsExtension ->
      (,True) .  second GAttrContent <$> addAttrsToSimple attrs
  GAttrContent cattrGI
    | Just newAttrs <- mbAttrsExtension -> do
      typeName <- getUniqueTypeName possibleName.unXmlNameWN
      consName <- getUniqueConsName CnoRecord possibleName.unXmlNameWN
      newAttrFields <- concat <$> mapM (attributeToField typeName quals) newAttrs
      pure
        (( typeName
        , GAttrContent $ cattrGI
          { attributes = newAttrFields <> cattrGI.attributes
          , typeName = typeName
          , consName = consName
          }
        )
        , True
        )
  GSeq seq_
    | Just newAttrs <- mbAttrsExtension -> do
      typeName <- getUniqueTypeName possibleName.unXmlNameWN
      consName <- getUniqueConsName CnoRecord possibleName.unXmlNameWN
      newAttrFields <- concat <$> mapM (attributeToField typeName quals) newAttrs
      pure
        (( typeName
        , GSeq $ seq_
          { attributes = newAttrFields <> seq_.attributes
          , typeName = typeName
          , consName = consName
          }
        )
        , True
        )
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
    typeName <- getUniqueTypeName possibleName.unXmlNameWN
    consName <- getUniqueConsName CnoRecord possibleName.unXmlNameWN
    attrFields <- concat <$> mapM (attributeToField typeName quals) attrs
    pure 
      ( typeName
      , ContentWithAttrsGI
      { typeName
      , consName
      , attributes = attrFields
      , content = FieldGI
        { haskellName = HaskellFieldName "content"
        , typeName = typeNoAttrs baseType GBaseType
        , inTagInfo = Nothing
        }
      })

  mbAttrsExtension :: Maybe (NE.NonEmpty Attr)
  mbAttrsExtension = case mixin of
    Complex{attrs, inner} -> do
      guard $ inner == Seq []
      NE.nonEmpty attrs
    _ -> Nothing

  isEmptyExtension :: Bool
  isEmptyExtension = case mixin of
    Complex{attrs, inner} -> do
      null attrs && inner `elem` [Seq [], Choice [], All []]
    _ -> False

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

mkListDeclaration :: ListGI -> (TyData, TyCon, TyType)
mkListDeclaration lgi =
  ( TyData $ B.byteString lgi.typeName.unHaskellTypeName
  , TyCon $ B.byteString lgi.consName.unHaskellConsName
  , TyType $ B.byteString $ mconcat ["[", lgi.itemType.unHaskellTypeName, "]"]
  )

generateContentTypeParseFunc :: HaskellTypeName -> FunctionBody
generateContentTypeParseFunc typeName = FunctionBody $ runCodeWriter $
  out1 (getParserNameForType typeName <> " = parseString")

generateNewtypeExtractFunc :: NewtypeGI -> FunctionBody
generateNewtypeExtractFunc ngi = FunctionBody $ runCodeWriter do
  let typeName = ngi.typeName
      consName = ngi.consName
      wrappedName = ngi.wrappedType.type_
  out1 [qc|{getParseRawFuncName typeName} =|]
  withIndent1 do
    out1 [qc|fmap {consName} . {getParseRawFuncName wrappedName}|]
  out1 [qc|extract{typeName}Content ofs =|]
  withIndent1 do
    out1 [qc|first {consName} $ extract{wrappedName}Content ofs|]

getParseRawFuncName :: HaskellTypeName -> String
getParseRawFuncName typeName = [qc|parse{typeName}Raw|]

generateEnumExtractFunc :: EnumGI -> FunctionBody
generateEnumExtractFunc en = FunctionBody $ runCodeWriter do
  let recType = en.typeName
  out1 [qc|{getParseRawFuncName recType} = \case|]
  withIndent1 do
    for_ en.constrs \(xmlName, haskellCon) ->
      out1 [qc|"{xmlName}" -> pure {haskellCon}|]
    out1 [qc|unknown -> error $ "unknown enum value: " <> show unknown|]

  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 do
    out1 [qc|extractAndParse {getParseRawFuncName recType} ofs|]

generateListExtractFunc :: ListGI -> FunctionBody
generateListExtractFunc lgi = FunctionBody $ runCodeWriter do
  let recType = lgi.typeName
      consName = lgi.consName
      baseType = lgi.itemType
  out1 [qc|extract{recType}Content =|]
  withIndent1 do
    out1 [qc|first {consName} . extractAndParse (traverse parse{baseType}Raw . BSC.words)|]

registerGI :: GIType -> CG ()
registerGI = \case
  GBaseType -> pure ()
  GAttrContent cgi -> registerAttrContent cgi
  GSeq seq_ -> registerSequenceGI seq_
  GChoice ch -> registerChoiceGI ch
  GEnum en -> registerEnumGI en
  GWrapper nwt -> registerNewtypeGI nwt
  GList lgi -> registerListGI lgi

registerListGI :: ListGI -> CG ()
registerListGI lgi = do
  registerDataDeclaration $ Newtype $ mkListDeclaration lgi
  registerParseFunction $ generateContentTypeParseFunc lgi.typeName
  registerExtractionFunction $ generateListExtractFunc lgi

registerEnumGI :: EnumGI -> CG ()
registerEnumGI e = do
  registerDataDeclaration $ Alg $ mkEnumTypeDeclaration e
  registerParseFunction $ generateContentTypeParseFunc e.typeName
  registerExtractionFunction $ generateEnumExtractFunc e

registerNewtypeGI :: NewtypeGI -> CG ()
registerNewtypeGI ngi = do
  registerDataDeclaration $ Newtype $ mkNewtypeDeclaration ngi
  registerParseFunction $ generateContentTypeParseFunc ngi.typeName
  registerExtractionFunction $ generateNewtypeExtractFunc ngi

registerNamedType :: XmlNameWN -> Namespace -> TypeWithAttrs -> CG ()
registerNamedType xmlName namespace haskellType = do
  knownTypes %= Map.alter (Just . ((namespace, haskellType) :) . fromMaybe []) xmlName

processSchemaNamedType :: QualNamespace -> Namespace -> (XmlNameWN, Type) -> CG TypeWithAttrs
processSchemaNamedType quals namespace (tName, tDef) = do
  q <- Lens.use knownTypes
  case Map.lookup tName q of
    Just q_
      | Just w_ <- List.lookup namespace q_ -> pure w_
    _ -> do
      haskellTypeName <- processType quals (Just tName) tDef
      registerNamedType tName namespace haskellTypeName
      pure haskellTypeName

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
    outCodeLine "{-# LANGUAGE TupleSections #-}"
    -- TODO also add in parser generator
    --
    --
    outCodeLine "module XMLSchema where"
    outCodeLine (basePrologue isUnsafe)

identity :: p -> p
identity x = x


