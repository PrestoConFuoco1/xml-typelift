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
{-# LANGUAGE MultiWayIf #-}
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
import Text.Interpolation.Nyan
import Data.Coerce
import Data.Hashable

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

outCodeMultiLines :: String -> CG ()
outCodeMultiLines msg = do
  let ls = lines msg
  mapM_ outCodeLine' ls

withIndent :: CG a -> CG a
withIndent act = do -- TODO use `bracket`
    incIndent
    r <- act
    decIndent
    return r

codegen :: GenerateOpts -> Schema -> IO String
codegen c sch =
  codegen' c sch $ generateParser2 False c sch

withFourmoluDisable :: CG a -> CG a
withFourmoluDisable action = do
  outCodeLine' "{- FOURMOLU_DISABLE -}"
  res <- action
  outCodeLine' "{- FOURMOLU_ENABLE -}"
  pure res

generateParser2 :: Bool -> GenerateOpts -> Schema -> CG ()
generateParser2 genParser opts@GenerateOpts{isGenerateMainFunction, topName} schema = withFourmoluDisable do
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
      when isGenerateMainFunction $ generateMainFunction opts

generateParserInternalStructures :: CG ()
generateParserInternalStructures = do
    outCodeLine [qc|-- | Internal representation of TopLevel|]
    outCodeLine [qc|data TopLevelInternal = TopLevelInternal !ByteString !(V.Vector Int) deriving (G.Generic, NFData, Show)|] -- TODO qualify all imports to avoid name clush
    outCodeLine ""

eltToRepeatedness :: Element -> Repeatedness
eltToRepeatedness (Element 0 Unbounded     _ _ _ _) = RepMany
eltToRepeatedness (Element 0 (MaxOccurs 1) _ _ _ _) = RepMaybe
eltToRepeatedness (Element 0 _             _ _ _ _) = RepMany
eltToRepeatedness (Element 1 (MaxOccurs 1) _ _ _ _) = RepOnce
eltToRepeatedness (Element 1 _             _ _ _ _) = RepMany
eltToRepeatedness (Element m Unbounded     _ _ _ _) = RepNotLess m
eltToRepeatedness (Element m (MaxOccurs n) _ _ _ _) = RepRange m n

generateParserInternalArray1 :: GenerateOpts -> (Element, TypeWithAttrs) -> CG ()
generateParserInternalArray1 GenerateOpts{isUnsafe} (topEl, topType) = do
    outCodeLine [qc|-- PARSER --|]
    -- Generate parser header
    let topTag = eName topEl
        topName = unHaskellTypeName $ mkHaskellTypeName topTag
    when (minOccurs topEl /= 1) $ parseErrorBs topName [qc|Wrong minOccurs = {minOccurs topEl}|]
    when (maxOccurs topEl /= MaxOccurs 1) $ parseErrorBs topName [qc|Wrong maxOccurs = {maxOccurs topEl}|]
    let repeatedness = RepOnce
    outCodeLine' [qc|parseTopLevelToArray :: ByteString -> TopLevelInternal|]
    outCodeLine' [qc|parseTopLevelToArray bs = TopLevelInternal bs $ V.create $ do|]
    withIndent $ do
        outCodeLine' [qc|vec_ <- {vecNew} ((max 1 (BS.length bs `div` 7)) * 2)|] -- TODO add code to strip vector
        outCodeLine' [qc|farthest    <- STRef.newSTRefU 0 -- farthest index so far|]
        outCodeLine' [qc|farthestTag <- STRef.newSTRef ("<none>" :: ByteString)|]
        outCodeLine' [qc|parseAttrsResultRef <- STRef.newSTRefU (0 :: Int)|]
        outCodeLine' [qc|let|]
        withIndent $ do
            outCodeLine' [qc|parse{topName} vec = do|]
            withIndent $ do
                outCodeLine' [qc|{vecWrite} vec 0# 0#|]
                outCodeLine' [qc|let arrOfs0 = 0#|]
                outCodeLine' [qc|let strOfs0 = skipSpaces (skipHeader (skipSpaces 0#))|]
                let
                  parseElementCall = generateParseElementCall ("arrOfs0", "strOfs0") (Just (topTag, repeatedness)) topType
                outCodeLine' [qc|_ <- {parseElementCall}|]
                outCodeLine' [qc|return ()|]
                outCodeLine' [qc|where|]
                parseFuncs_ <- Lens.use parseFunctions
                withIndent $ do
                    mapM_ generateFunction parseFuncs_
                    generateAuxiliaryFunctionsIA
        outCodeLine' [qc|parse{topName} vec_|]
        outCodeLine' [qc|return vec_|]
  where
    vecNew, vecWrite, bsIndex :: String
    vecNew   | isUnsafe  = "V.unsafeNew"
             | otherwise = "V.new"
--    vecWrite | isUnsafe  = "V.unsafeWrite"
--             | otherwise = "V.write"
    vecWrite = "vecWrite"
--    bsIndex  | isUnsafe  = "BSU.unsafeIndex"
--             | otherwise = "BS.index"
    bsIndex = "bsIndex"
    generateAuxiliaryFunctionsIA = do
        --
        -- TODO read this from file!
        --
      outCodeMultiLines [int|D|

lastBsIndex = BS.length bs - 1

{-# INLINE bsIndex #-}
bsIndex bs_ ix_
  | I# ix_ < 0 = throw $ InvalidIndex (I# ix_) bs
  | I# ix_ > lastBsIndex = throw $ InvalidIndex (I# ix_) bs
  | otherwise = bs_ `BSU.unsafeIndex` (I# ix_)

{-# INLINE vecWrite #-}
vecWrite vec arrOfs n = V.unsafeWrite vec (I# arrOfs) (I# n)

{-# INLINE unI# #-}
unI# (I# n) = n

{-# INLINE toError #-}
toError tag (strOfs :: Int#) act = do
    act >>= \\case
        res@(ArrStrOfss arrOfs' _) ->
          if I# arrOfs' < 0
          then failExp ("<" <> tag) strOfs
          else return res

{-# INLINE isBeforeTag #-}
isBeforeTag :: Word8 -> Bool
isBeforeTag c = c == openTagChar || c == slashChar || c == colonChar

{-# INLINE isAfterTag #-}
isAfterTag :: Word8 -> Bool
isAfterTag c = isSpaceChar c || c == closeTagChar || c == slashChar

{-# INLINE isQualDelim #-}
isQualDelim :: Word8 -> Bool
isQualDelim c = c == colonChar

{-# INLINE getTagName #-}
getTagName :: Int# -> XMLString
getTagName strOfsOld = do
  let strOfs = skipToOpenTag strOfsOld +# 1#
      noColon = BS.takeWhile (\\c -> not (isAfterTag c || isQualDelim c)) $ BS.drop (I# strOfs) bs
      afterNoColonOfs = strOfs +# unI# (BS.length noColon)
  if bs `bsIndex` afterNoColonOfs /= colonChar
  then noColon
  else BS.takeWhile (not . isAfterTag) $ BS.drop (I# (afterNoColonOfs +# 1#)) bs

{-# INLINE getAfterTagOffset #-}
getAfterTagOffset :: Int# -> Int#
getAfterTagOffset strOfs =
  if not (isAfterTag $ bsIndex bs strOfs)
  then getAfterTagOffset (strOfs +# 1#)
  else strOfs

{-
{-# INLINE getAttrName #-}
getAttrName :: Int# -> XMLString
getAttrName strOfs = BS.takeWhile (/= eqChar) $ BS.drop (I# strOfs) bs
-}

{-# INLINE inOneTag #-}
inOneTag          tag arrOfs strOfs inParser = toError tag strOfs $ inOneTag' tag arrOfs strOfs inParser
{-# INLINE inOneTagWithAttrs #-}
inOneTagWithAttrs attrAlloc attrRouting tag arrOfs strOfs inParser =
  toError tag strOfs $ inOneTagWithAttrs' attrAlloc attrRouting tag arrOfs strOfs inParser
{-# INLINE inOneTagWithAttrs' #-}
inOneTagWithAttrs' attrAlloc attrRouting tag (arrOfs :: Int#) (strOfs :: Int#) inParser = do
    let tagStrOfs = skipToOpenTag strOfs +# 1#
    q <- parseTagWithAttrs attrAlloc attrRouting tag arrOfs tagStrOfs
    case q of
      EnsureAttrTagResult ofs' arrOfs' isOpenTagEmpty
        | I# ofs' < 0 -> do
            updateFarthest tag tagStrOfs
            return emptyArrStrOfss
        | isOpenTagEmpty -> do
            ArrStrOfss arrOfs strOfs <- inParser arrOfs' (ofs' -# 1#)
            return $ ArrStrOfss arrOfs ofs'
        | otherwise -> do
            ArrStrOfss arrOfs strOfs <- inParser arrOfs' ofs'
            let ofs'' = skipToOpenTag strOfs
            if bs `bsIndex` (ofs'' +# 1#) == slashChar then do
                case ensureTag False tag (ofs'' +# 2#) of
                  EnsureTagResult ofs''' _
                    | I# ofs''' < 0 -> do
                        updateFarthest tag tagStrOfs
                        return emptyArrStrOfss
                    | otherwise -> pure $ ArrStrOfss arrOfs ofs'''
            else do
                return emptyArrStrOfss
{-# INLINE inOneTag' #-}
inOneTag' tag (arrOfs :: Int#) (strOfs :: Int#) inParser = do
    let tagOfs = skipToOpenTag strOfs +# 1#
    case ensureTag True tag tagOfs of
      EnsureTagResult ofs' isOpenTagEmpty
        | I# ofs' < 0 -> do
            updateFarthest tag tagOfs
            return emptyArrStrOfss
        | isOpenTagEmpty -> do
            ArrStrOfss arrOfs strOfs <- inParser arrOfs (ofs' -# 1#) -- TODO points to special unparseable place
            return $ ArrStrOfss arrOfs ofs'
        | otherwise -> do
            ArrStrOfss arrOfs strOfs <- inParser arrOfs ofs'
            let ofs'' = skipToOpenTag strOfs
            if bs `#{bsIndex}` (ofs'' +# 1#) == slashChar then do
                case ensureTag False tag (ofs'' +# 2#) of
                  EnsureTagResult ofs''' _
                    | I# ofs''' < 0 -> do
                        updateFarthest tag tagOfs
                        return emptyArrStrOfss
                    | otherwise -> return $ ArrStrOfss arrOfs ofs'''
            else do
                return emptyArrStrOfss
{-# INLINE inMaybeTag #-}
inMaybeTag tag arrOfs strOfs inParser = inMaybeTag' tag arrOfs strOfs inParser
{-# INLINE inMaybeTagWithAttrs #-}
inMaybeTagWithAttrs tag arrOfs strOfs inParser = inMaybeTagWithAttrs' tag arrOfs strOfs inParser
{-# INLINE inMaybeTagWithAttrs' #-}
inMaybeTagWithAttrs' attrAlloc attrRouting tag arrOfs strOfs inParser = do
    vecWrite vec arrOfs 1#
    inOneTagWithAttrs' attrAlloc attrRouting tag (arrOfs +# 1#) strOfs inParser >>= \\case
        res@(ArrStrOfss arrOfs' _) ->
          if I# arrOfs' < 0
          then do
            updateFarthest tag strOfs
            #{vecWrite} vec arrOfs 0#
            return $! ArrStrOfss (arrOfs +# 1#) strOfs
          else return res
{-# INLINE inMaybeTag' #-}
inMaybeTag' tag arrOfs strOfs inParser = do
    vecWrite vec arrOfs 1#
    inOneTag' tag (arrOfs +# 1#) strOfs inParser >>= \\case
        res@(ArrStrOfss arrOfs' _) ->
          if I# arrOfs' < 0
          then do
            updateFarthest tag strOfs
            #{vecWrite} vec arrOfs 0#
            return $! ArrStrOfss (arrOfs +# 1#) strOfs
          else return res
{-# INLINE inManyTags #-}
inManyTags tag arrOfs strOfs inParser = inManyTags' tag arrOfs strOfs inParser
{-# INLINE inManyTagsWithAttrs #-}
inManyTagsWithAttrs tag arrOfs strOfs inParser = inManyTagsWithAttrs' tag arrOfs strOfs inParser
{-# INLINE inManyTags' #-}
inManyTags' tag (arrOfs :: Int#) (strOfs :: Int#) inParser = do
  go 0 (arrOfs +# 1#) strOfs
  where
    go cnt arrOfs' strOfs' =
          inOneTag' tag arrOfs' strOfs' inParser >>= \\case
            ArrStrOfss arrOfs'' strOfs'' ->
              if I# arrOfs'' < 0
              then do
                updateFarthest tag strOfs'
                #{vecWrite} vec arrOfs (unI# cnt)
                return $! ArrStrOfss arrOfs' strOfs'
              else go (cnt + 1) arrOfs'' strOfs''
{-# INLINE inManyTagsWithAttrs' #-}
inManyTagsWithAttrs' attrAlloc attrRouting tag (arrOfs :: Int#) (strOfs :: Int#) inParser = do
  go 0 (arrOfs +# 1#) strOfs
  where
    go cnt arrOfs' strOfs' =
          inOneTagWithAttrs' attrAlloc attrRouting tag arrOfs' strOfs' inParser >>= \\case
            ArrStrOfss arrOfs'' strOfs'' ->
              if I# arrOfs'' < 0
              then do
                updateFarthest tag strOfs'
                #{vecWrite} vec arrOfs (unI# cnt)
                return $! ArrStrOfss arrOfs' strOfs'
              else go (cnt + 1) arrOfs'' strOfs''

{-# INLINE isGivenTagBeforeOffset #-}
isGivenTagBeforeOffset expectedTag ofsToEnd =
  expectedTag `BS.isSuffixOf` BS.take (I# ofsToEnd) bs
    && isBeforeTag (bsIndex bs (ofsToEnd -# unI# (BS.length expectedTag) -# 1#))

{-# INLINE ensureTag #-}
ensureTag True expectedTag ofs
  | isGivenTagBeforeOffset expectedTag ofsToEnd =
      if bs `#{bsIndex}` ofsToEnd == closeTagChar
        then EnsureTagResult (ofsToEnd +# 1#) False
      else
        let ofs' = skipToCloseTag (ofs +# unI# (BS.length expectedTag))
         in EnsureTagResult (ofs' +# 1#) (bs `#{bsIndex}` (ofs' -# 1#) == slashChar)
  | otherwise = emptyEnsureTagResult
  where
    ofsToEnd = getAfterTagOffset ofs
ensureTag False expectedTag ofs
  | isGivenTagBeforeOffset expectedTag ofsToEnd
        = EnsureTagResult (ofsToEnd +# 1#) False
  | otherwise
        = emptyEnsureTagResult
  where
    ofsToEnd = getAfterTagOffset ofs
parseAttributes attrRouting strOfs (arrOfs :: Int#) = do
  let ofs1 = skipSpaces strOfs
      curCh = bs `bsIndex` ofs1 
  if curCh == slashChar || curCh == closeTagChar
    then STRef.writeSTRefU parseAttrsResultRef (I# ofs1)
    else do
    let
    --   attrName = getAttrName ofs1
    --   ofsAttrContent = ofs1 +# unI# (BS.length attrName) +# 2#
    -- I# attrContentEnd <- parseAttrContent (attrRouting arrOfs (unI# (hash attrName))) ofsAttrContent
      afterAttrOffset = skipTo eqChar ofs1
      attrLength = afterAttrOffset -# ofs1
      ofsAttrContent = afterAttrOffset +# 2#
      attrHash = unI# $ hash $ BSU.unsafeTake (I# attrLength) $ BSU.unsafeDrop (I# ofs1) bs
    I# attrContentEnd <- parseAttrContent (attrRouting arrOfs attrHash) ofsAttrContent
    parseAttributes attrRouting (attrContentEnd +# 1#) arrOfs
{-# INLINE parseTagWithAttrs #-}
parseTagWithAttrs attrAlloc attrRouting expectedTag (arrOfs :: Int#) ofs
  | isGivenTagBeforeOffset expectedTag ofsToEnd = do
      I# arrOfsAfterAttrs <- attrAlloc arrOfs
      if bs `bsIndex` ofsToEnd == closeTagChar
        then pure $ EnsureAttrTagResult (ofsToEnd +# 1#) arrOfsAfterAttrs False
      else do
        parseAttributes attrRouting ofsToEnd arrOfs
        I# strOfsAfterAttrs <- STRef.readSTRefU parseAttrsResultRef
        let ofs' = skipToCloseTag strOfsAfterAttrs
        pure $ EnsureAttrTagResult (ofs' +# 1#) arrOfsAfterAttrs (bs `bsIndex` (ofs' -# 1#) == slashChar)
  | otherwise = pure emptyEnsureAttrTagResult
  where
    ofsToEnd = getAfterTagOffset ofs


{-# INLINE failExp #-}
failExp _expStr (_ofs :: Int#) = do
  failOfs <- STRef.readSTRefU farthest
  failTag <- STRef.readSTRef farthestTag
  throw $ XmlParsingError failOfs failTag ErrorContext{offset=failOfs, input=bs}

{-# INLINE updateFarthest #-}
updateFarthest tag tagOfs = do
  f <- STRef.readSTRefU farthest
  when (I# tagOfs > f) $ do
    STRef.writeSTRefU farthest (I# tagOfs)
    STRef.writeSTRef farthestTag tag
{-# INLINE parseXMLStringContent #-}
parseXMLStringContent = parseString
{-# INLINE parseAttrContent #-}
parseAttrContent arrAttrLocation strStart = do
  let strEnd = skipTo dquoteChar strStart
  when (I# arrAttrLocation >= 0) do
    vecWrite vec arrAttrLocation     strStart
    vecWrite vec (arrAttrLocation +# 1#) (strEnd -# strStart)
  return $ I# strEnd

{-# INLINE parseString #-}
parseString arrStart strStart = do
  let strEnd = skipToOpenTag strStart
  #{vecWrite} vec arrStart     strStart
  #{vecWrite} vec (arrStart +# 1#) (strEnd -# strStart)
  pure $ ArrStrOfss (arrStart +# 2#) strEnd
  |]
      let
        simpleTypes =
          [ "Scientific", "DateTime", "Duration", "GYearMonth"
          , "GYear", "Bool", "Double", "Float", "GMonth"
          , "Integer", "Int", "Int64", "Day", "TimeOfDay"
          , "XDateTime", "XTime", "Boolean" :: String
          ]
      forM_ simpleTypes \sty -> do
        outCodeLine' [int||{-# INLINE parse#{sty}Content #-}|]
        outCodeLine' [int||parse#{sty}Content = parseString|]
      outCodeMultiLines [int|D|
{-# INLINE parseUnitContent #-}
parseUnitContent arrStart strStart =
  pure $ ArrStrOfss arrStart (parseUnitContentRec (0 :: Int) strStart)
parseUnitContentRec level strStart = do
  let startTagIdx = skipToOpenTag strStart
      endTagIdx = skipToCloseTag startTagIdx
  if (bs `bsIndex` (startTagIdx +# 1#)) == slashChar
    then
      -- it's closing tag
      (if level == 0 then startTagIdx else parseUnitContentRec (level - 1) endTagIdx)
    else if bs `bsIndex` (endTagIdx -# 1#) == slashChar
      -- empty tag, parsing further on the same level
      then parseUnitContentRec level endTagIdx
      -- open tag, one level deeper
      else parseUnitContentRec (level+1) endTagIdx

skipSpaces ofs
  | isSpaceChar (bs `#{bsIndex}` ofs) = skipSpaces (ofs +# 1#)
  | otherwise = ofs
{-# INLINE isSpaceChar #-}
isSpaceChar :: Word8 -> Bool
isSpaceChar c = c == 32 || c == 10 || c == 9 || c == 13
skipHeader :: Int# -> Int#
skipHeader ofs
  | bs `#{bsIndex}` ofs == openTagChar && bs `#{bsIndex}` (ofs +# 1#) == questionChar = skipToCloseTag (ofs +# 2#) +# 1#
  | otherwise = ofs
eqChar       = 61 -- '='
dquoteChar   = 34 -- '"'
slashChar    = 47 -- '<'
openTagChar  = 60 -- '<'
closeTagChar = 62 -- '>'
questionChar = 63 -- '?'
colonChar = 58 -- '?'
skipToCloseTag :: Int# -> Int#
skipToCloseTag ofs
  | bs `#{bsIndex}` ofs == closeTagChar = ofs
  | otherwise = skipToCloseTag (ofs +# 1#)
skipToOpenTag :: Int# -> Int#
skipToOpenTag ofs -- TODO: try to do this using memchr (elemIndex)
  | bs `#{bsIndex}` ofs == openTagChar = ofs
  | otherwise = skipToOpenTag (ofs +# 1#)
skipTo :: Word8 -> Int# -> Int#
skipTo c ofs
  | bs `#{bsIndex}` ofs == c = ofs
  | otherwise = skipTo c (ofs +# 1#)
  |]

generateParserExtractTopLevel1 ::
  HasCallStack =>
  GenerateOpts ->
  TypeWithAttrs ->
  CG ()
generateParserExtractTopLevel1 GenerateOpts{isUnsafe} topType = do
    let topTypeName = topType.type_
    outCodeLine' [qc|extractTopLevel :: TopLevelInternal -> TopLevel|]
    outCodeLine' [qc|extractTopLevel (TopLevelInternal bs arr) = getExtractResult $ extract{topTypeName}Content 0#|]
    withIndent $ do
        outCodeLine' "where"
        extractFuncs_ <- Lens.use extractFunctions
        withIndent $ do
            mapM_ generateFunction extractFuncs_
            generateAuxiliaryFunctions_
  where
    generateAuxiliaryFunctions_ = do
        let
          extrStrBody =
            if isUnsafe then
              [qc|extractStringContent ofs = ExtractResult (BSU.unsafeTake bslen $ BSU.unsafeDrop bsofs bs) (ofs +# 2#)|]
            else
              -- not working currently
              [qc|extractStringContent ofs = (BS.take bslen (BS.drop bsofs bs), ofs + 2)|]

        outCodeMultiLines [int|D|
{-# INLINE vecIndex #-}
vecIndex vec_ idx_ = vec_ `V.unsafeIndex` (I# idx_)

{-# INLINE extractStringContent #-}
extractStringContent :: Int# -> ExtractResult ByteString
#{extrStrBody :: String}
  where
    bsofs = arr #{index} ofs
    bslen = arr #{index} (ofs +# 1#)
{-# INLINE extractMaybe #-}
extractMaybe :: Int# -> (Int# -> ExtractResult a) -> ExtractResult (Maybe a)
extractMaybe ofs subextr
  | arr #{index} ofs == 0 = ExtractResult Nothing (ofs +# 1#)
  | otherwise                     = mapExtr Just (subextr (ofs +# 1#))
{-# INLINE extractAttribute #-}
extractAttribute :: Int# -> (Int# -> ExtractResult a) -> ExtractResult (Maybe a)
extractAttribute ofs subextr
  | arr `vecIndex` ofs == 0 = ExtractResult Nothing (ofs +# 2#)
  | otherwise                     = mapExtr Just (subextr ofs)

{-# INLINE extractMany #-}
extractMany :: Int# -> (Int# -> ExtractResult a) -> ExtractResult [a]
extractMany ofsInit subextr = extractMany' (ofsInit +# 1#) (arr `vecIndex` ofsInit) []
  where
    extractMany' ofs 0   acc = ExtractResult (reverse acc) ofs
    extractMany' ofs len acc =
      let !(ExtractResult v ofs') = subextr ofs
      in extractMany' ofs' (len - 1) (v : acc)

{-# INLINE extractUnitContent #-}
extractUnitContent :: Int# -> ExtractResult ()
extractUnitContent ofs = ExtractResult () ofs
{-# INLINE extractXMLStringContent #-}
extractXMLStringContent = extractStringContent
|]
        let
          typesUsingCustomShortParsers :: [(String, String)] =
            [ ("Duration", "parseDuration")
            , ("Double", "fmap realToFrac . parseScientificRaw")
            , ("Float", "fmap realToFrac . parseScientificRaw")
            , ("GYear", "parseIntegerRaw")
            , ("Int64", "fmap fromIntegral . parseIntRaw")
            ]
          typesUsingCustomParsers =
            ["Scientific", "XTime", "XDateTime", "Bool", "GYearMonth", "GMonth", "Day", "Int", "Integer"]
          mkParseRawTypeSig :: String -> String
          mkParseRawTypeSig t = [int||parse#{t}Raw :: ByteString -> Either String #{t}|]
          mkCustomParseRawBody :: String -> String -> String
          mkCustomParseRawBody t parse_ = [int||parse#{t}Raw = #{parse_}|]
        for_ typesUsingCustomShortParsers \(t, p) -> do
          outCodeLine' [int||{-# INLINE parse#{t}Raw #-}|]
          outCodeLine' $ mkParseRawTypeSig t
          outCodeLine' $ mkCustomParseRawBody t p
        for_ (typesUsingCustomParsers <> map fst typesUsingCustomShortParsers) \t -> do
          outCodeLine' [int||{-# INLINE extract#{t}Content #-}|]
          outCodeLine' [int||extract#{t}Content :: Int# -> ExtractResult #{t}|]
          outCodeLine' [int||extract#{t}Content = extractAndParse parse#{t}Raw|]

        outCodeMultiLines [int|D|
{-# INLINE parseXMLStringRaw #-}
parseXMLStringRaw :: ByteString -> Either String ByteString
parseXMLStringRaw = pure
{-# INLINE parseBoolRaw #-}
parseBoolRaw = \\case
    "true" -> Right True
    "1" -> Right True
    "false"-> Right False
    "0" -> Right False
    unexp -> Left $ "unexpected bool value: " <> show unexp

{-# INLINE extractAndParse #-}
extractAndParse :: (ByteString -> Either String a) -> Int# -> ExtractResult a
extractAndParse parser ofs = mapExtr (catchErr ofs parser) (extractStringContent ofs)

{-# INLINE catchErr #-}
catchErr :: Int# -> (ByteString -> Either String b) -> ByteString -> b
catchErr ofs f str = either (throwWithContext bs bsOfs . PrimitiveTypeParsingError str) id (f str)
  where !(I# bsOfs) = arr #{index} ofs

{-# INLINE runFlatparser #-}
runFlatparser :: ByteString -> FP.Parser String a -> Either String a
runFlatparser bsInp parser = fromFlatparseResult $ FP.runParser parser bsInp 

{-# INLINE fromFlatparseResult #-}
fromFlatparseResult :: FP.Result String a -> Either String a
fromFlatparseResult = \\case
  FP.OK res unconsumed -> do
    unless (BS.null unconsumed) (Left $ "unconsumed " <> show unconsumed)
    pure res
  FP.Fail -> Left "failed"
  FP.Err e -> Left e
fpSkipAsciiChar c = FP.skipSatisfyAscii (== c)

{-# INLINE parseGYearMonthRaw #-}
parseGYearMonthRaw :: ByteString -> Either String GYearMonth
parseGYearMonthRaw bsInp = runFlatparser bsInp do
  year <- FP.anyAsciiDecimalInteger
  fpSkipAsciiChar '-'
  month <- FP.anyAsciiDecimalInt
  pure $ YearMonth year month

{-# INLINE parseGMonthRaw #-}
parseGMonthRaw :: ByteString -> Either String GMonth
parseGMonthRaw bsInp = runFlatparser bsInp do
  fpSkipAsciiChar '-'
  fpSkipAsciiChar '-'
  month <- FP.anyAsciiDecimalInt
  pure month

{-# INLINE parseDayRaw #-}
parseDayRaw :: ByteString -> Either String Day
parseDayRaw bsInp = runFlatparser bsInp parseDayFlat

{-# INLINE parseDayFlat #-}
parseDayFlat :: FP.Parser String Day
parseDayFlat = do
  year <- FP.anyAsciiDecimalInteger
  fpSkipAsciiChar '-'
  month <- FP.anyAsciiDecimalInt
  fpSkipAsciiChar '-'
  day <- FP.anyAsciiDecimalInt
  pure $ fromGregorian year month day

{-# INLINE parseTimeOfDayFlat #-}
parseTimeOfDayFlat :: FP.Parser String TimeOfDay
parseTimeOfDayFlat = do
  hours <- FP.anyAsciiDecimalInt
  fpSkipAsciiChar ':'
  minutes <- FP.anyAsciiDecimalInt
  fpSkipAsciiChar ':'
  secondsInteger <- FP.anyAsciiDecimalInteger
  let
    mbSecondsFracParser = asum
      [ fpSkipAsciiChar '.' >> fmap Just FP.anyAsciiDecimalInteger
      , pure Nothing
      ]
  secondsFrac <- FP.withByteString mbSecondsFracParser \\mSf sBs ->
    case mSf of
      Nothing -> pure 0
      Just sF -> do
        let len = BS.length sBs - 1
        if len <= 12
        then pure $ sF * 10 ^ (12 - len)
        else pure $ sF `div` (10 ^ (len - 12))

  let seconds = MkFixed $ secondsInteger * 1_000_000_000_000 + secondsFrac
  pure $ TimeOfDay hours minutes seconds

{-# INLINE parseXDateTimeRaw #-}
parseXDateTimeRaw :: ByteString -> Either String XDateTime
parseXDateTimeRaw bsInp = runFlatparser bsInp do
  day <- parseDayFlat
  fpSkipAsciiChar 'T'
  timeOfDay <- parseTimeOfDayFlat
  mbTimeZone <- FP.optional $ parseTimeZoneFlat
  FP.skipMany $ FP.skipSatisfyAscii Data.Char.isSpace
  pure WithTimezone
    { value = LocalTime
      { localDay = day
      , localTimeOfDay = timeOfDay
      }
    , timezone = mbTimeZone
    }

{-# INLINE parseXTimeRaw #-}
parseXTimeRaw :: ByteString -> Either String XTime
parseXTimeRaw bsInp = runFlatparser bsInp do
  timeOfDay <- parseTimeOfDayFlat
  mbTimeZone <- FP.optional parseTimeZoneFlat
  FP.skipMany $ FP.skipSatisfyAscii Data.Char.isSpace
  pure WithTimezone
    { value = timeOfDay
    , timezone = mbTimeZone
    }

{-# INLINE parseTimeZoneFlat #-}
parseTimeZoneFlat :: FP.Parser String TimeZone
parseTimeZoneFlat = do
  let zUtc = fpSkipAsciiChar 'Z' >> pure utc
      offsetTz = do
        sign :: Int <- asum [fpSkipAsciiChar '+' >> pure 1, fpSkipAsciiChar '-' >> pure (-1)]
        tzHr <- FP.anyAsciiDecimalInt
        fpSkipAsciiChar ':'
        tzMin <- FP.anyAsciiDecimalInt
        pure $ minutesToTimeZone $ sign * (tzHr * 60 + tzMin)
  asum [zUtc, offsetTz]

{-# INLINE getSign #-}
getSign :: FP.Parser String Int
getSign = do
  let
    getSign' = do
      c <- FP.satisfyAscii (\\c -> c == '+' || c == '-')
      pure $ if c == '-' then (-1) else 1
  getSign' <|> pure 1

{-# INLINE parseScientificRaw #-}
parseScientificRaw :: ByteString -> Either String Scientific
parseScientificRaw bsInp = runFlatparser bsInp do
  coefSign <- getSign
  n <- FP.anyAsciiDecimalInteger
  (SP nWithFrac afterPointExp) <- asum
    [ do
      fpSkipAsciiChar '.'
      FP.withByteString FP.anyAsciiDecimalInteger \\m mBs ->
        pure $ SP (n * (10 ^ BS.length mBs) + m) (negate $ BS.length mBs)
    , pure $ SP n 0
    ]
  let
    eP = do
      eSign <- getSign
      e <- FP.anyAsciiDecimalInt
      pure $ eSign * e
    isE c = c == 'e' || c == 'E'
  exp_ <- asum
    [ do
      FP.skipSatisfyAscii isE
      eP
    , pure 0
    ]
  pure $ scientific (fromIntegral coefSign * nWithFrac) (afterPointExp + exp_)

{-# INLINE parseIntRaw #-}
parseIntRaw :: ByteString -> Either String Int
parseIntRaw bsInp = runFlatparser bsInp do
  coefSign <- getSign
  n <- FP.anyAsciiDecimalInt
  pure $ coefSign * n

{-# INLINE parseIntegerRaw #-}
parseIntegerRaw :: ByteString -> Either String Integer
parseIntegerRaw bsInp = runFlatparser bsInp do
  coefSign <- getSign
  n <- FP.anyAsciiDecimalInteger
  pure $ fromIntegral coefSign * n

|]
    index = "`vecIndex`" :: String

    --index | isUnsafe  = "`V.unsafeIndex`" :: String
      --    | otherwise = "V.!"


generateParserTop :: CG ()
generateParserTop = do
    outCodeLine "parse :: ByteString -> Either XmlTypeliftException TopLevel" -- TODO
    outCodeLine "parse bs = unsafePerformIO $ try $ evaluate $ extractTopLevel $ parseTopLevelToArray bs"

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
                    outCodeLine' [qc|hPutStrLn stderr $ "Error while parsing \"" ++ filename ++ "\": " ++ ppXmlTypeliftException err|]
                    outCodeLine' [qc|exitFailure|]
                outCodeLine' [qc|Right result -> do|]
                withIndent $ do
                    outCodeLine' [qc|if isPrinting then do|]
                    withIndent $ do
                        outCodeLine' [qc|putStrLn filename|]
                        if isUnsafe then
                            outCodeLine' [qc|print result|]
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
    , TyType $ mkTypeWithCardinality True inTagInfo $ B.byteString conType.type_.unHaskellTypeName
    )
  )

mkSequenceTypeDeclaration :: SequenceGI -> (TyData, [Record])
mkSequenceTypeDeclaration s =
  (TyData $ B.byteString s.typeName.unHaskellTypeName
  , [ ( TyCon $ B.byteString s.consName.unHaskellConsName
      , map mkAttrFieldDeclaration s.attributes <> map (mkFieldDeclaration False) s.fields
      )
    ]
  )

mkAttrContentTypeDeclaration :: ContentWithAttrsGI -> (TyData, [Record])
mkAttrContentTypeDeclaration cgi =
  ( TyData $ B.byteString cgi.typeName.unHaskellTypeName
  , [ ( TyCon $ B.byteString cgi.consName.unHaskellConsName
      , map mkAttrFieldDeclaration cgi.attributes <> map (mkFieldDeclaration False) [cgi.content]
      )
    ]
  )

mkFieldDeclaration :: Bool -> FieldGI -> TyField
mkFieldDeclaration wrapApplication fld =
  ( TyFieldName $ B.byteString fld.haskellName.unHaskellFieldName
  , TyType $ mkTypeWithCardinality wrapApplication fld.inTagInfo $ B.byteString fld.typeName.type_.unHaskellTypeName
  )

mkTypeWithCardinality :: Bool -> Maybe (a1, Repeatedness) -> B.Builder -> B.Builder
mkTypeWithCardinality wrapApplication inTagInfo x = case inTagInfo of
  Nothing -> x
  Just (_, card) -> case card of
    RepMaybe -> wrapParens $ "Maybe " <> x
    RepOnce -> x
    _ -> "[" <> x <> "]"
  where
  wrapParens txt =
    if wrapApplication
    then "(" <> txt <> ")"
    else txt

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
  let funcName = getParserNameForType cgi.typeName
  emitInline funcName
  out1 (funcName <> " = " <> getParserNameForType cgi.content.typeName.type_)

emitInline :: String -> CodeWriter
emitInline funcName = out1 $ "{-# INLINE " <> funcName <> " #-}"

generateSequenceParseFunctionBody :: SequenceGI -> FunctionBody
generateSequenceParseFunctionBody s = FunctionBody $ runCodeWriter do
  generateAttrsAllocation
    TypeWithAttrs { type_ = s.typeName, giType = GSeq s }
  -- let funcName = getParserNameForType s.typeName
  -- emitInline funcName
  -- -- otherwise the generated module will never compile
  out1 (getParserNameForType s.typeName <> " arrStart strStart = do")
  withIndent1 do
    let (arrStart, strStart) = ("arrStart", "strStart")
        fields = {- s.attributes <> -} s.fields
    let ofsNames' = ((arrStart, strStart) : [ ( [qc|arrOfs{i}|], [qc|strOfs{i}|]) | i <- [(1::Int)..]])
                    :: [(XMLString, XMLString)]
        ofsNames = zip ofsNames' (tail ofsNames')
        (arrRet, strRet) = ofsNames' !! length fields
    forM_ (zip ofsNames fields) $ \((oldOffsets, (arrOfs', strOfs')), field) -> do
      out1 [qc|ArrStrOfss {arrOfs'} {strOfs'} <- do|]
      withIndent1 do
        -- offsetsAfterAllocGen <- generateAttrsAllocation oldOffsets field.typeName
        out1 $ generateParseElementCall oldOffsets field.inTagInfo field.typeName
    out1 [qc|pure $! ArrStrOfss {arrRet} {strRet}|]

generateAttrsAllocation ::
  TypeWithAttrs ->
  CodeWriter
generateAttrsAllocation TypeWithAttrs{type_, giType} =
  withPresentAttrs \attrs -> do
    let attrsNum = length attrs
    let totalAllocLen = 2*attrsNum
        allocatorName = getAttrsAllocatorName type_
    emitInline allocatorName
    out1 [qc|{allocatorName} ofs = do|]
    withIndent1 do
      out1 [qc|forM_ [0..{totalAllocLen - 1}] $ \(I# i) -> vecWrite vec (ofs +# i) 0#|]
      out1 [qc|pure $ I# (ofs +# {totalAllocLen}#)|]
    let routingName = getAttrsRoutingName type_
    emitInline routingName
    out1 [qc|{routingName} (ofs :: Int#) = \case|]
    withIndent1 $ do
      forM_ (zip [0::Int, 2 .. ] $ NE.toList attrs) \(ofs, attr) -> do
        let attrHash = hash attr
        out1 [qc|x | I# x == hash ("{attr}" :: ByteString) -> ofs +# {ofs}#|]
      out1 [qc|_ -> (-1#)|]
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

getAttrsRoutingName :: HaskellTypeName -> String
getAttrsRoutingName t = [qc|get{t}AttrOffset|]

getAttrsAllocatorName :: HaskellTypeName -> String
getAttrsAllocatorName t = [qc|allocate{t}Attrs|]

generateChoiceParseFunctionBody :: ChoiceGI -> FunctionBody
generateChoiceParseFunctionBody ch = FunctionBody $ runCodeWriter $ do
  let funcName = getParserNameForType ch.typeName
  -- emitInline funcName
  -- -- otherwise the generated module will never compile
  out1 (funcName <> " arrStart strStart = do") >> withIndent1 do
    out1 [qc|let tagName = getTagName strStart|]
    out1 [qc|case tagName of|]
    withIndent1 $ forM_ (zip ch.alts [0 :: Int ..]) \((inTagInfo, possibleFirstTags, _cons, type_), altIdx) -> do
      let vecWrite {- | isUnsafe -} = "vecWrite" :: B.Builder
          captureCon = [qc|{vecWrite} vec arrStart {altIdx}#|] :: B.Builder
          parseFunc1 =
            generateParseElementCall ("(arrStart +# 1#)", "strStart") inTagInfo type_
      forM_ possibleFirstTags \firstTag ->
        out1 [qc|"{firstTag}" -> {captureCon} >> {parseFunc1}|]
    withIndent1 $ do
      let totalPossibleFirstTags = concatMap get2Of4 ch.alts
      out1 [qc|unknown -> throwWithContext bs (1# +# skipToOpenTag (strStart +# 1#)) $ UnknownChoiceTag unknown "{typeName}" {totalPossibleFirstTags}|]
  where
  typeName = ch.typeName
  get2Of4 (_, x, _, _) = x

generateChoiceExtractFunctionBody :: ChoiceGI -> FunctionBody
generateChoiceExtractFunctionBody ch = FunctionBody $ runCodeWriter do
  let chName = ch.typeName
  let extrFuncName = [qc|extract{chName}Content|] :: String
  emitInline extrFuncName
  out1 [qc|{extrFuncName} ofs = do|]
  withIndent1 do
    let vecIndex = "`vecIndex`" :: String
    out1 [qc|let altIdx = arr {vecIndex} ofs|]
    out1 [qc|case altIdx of|]
    withIndent1 $ forM_ (zip ch.alts [0 :: Int ..]) \((inTagInfo, _possibleFirstTags, cons_, type_), altIdx) -> do
      let typeName = type_.type_
      let extractor = getExtractorNameWithQuant "(ofs +# 1#)" inTagInfo typeName
      out1 [qc|{altIdx} -> mapExtr {cons_} $ {extractor}|]
    withIndent1 $ do
      out1 [qc|wrongIndex -> throw $ InternalErrorChoiceInvalidIndex wrongIndex "{chName}"|]

generateSingleAttrExtract :: HaskellTypeName -> AttrFieldGI -> Int -> String
generateSingleAttrExtract recType attr aIdx = do
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
      then [qc|mapExtr (fromMaybe $ throw $ RequiredAttributeMissing "{haskellAttrName}" "{recType}") $ |]
      else "" :: String
    finalExtractorType :: String =
      if attrRequired
      then [qc|ExtractResult {haskellTypeName}|]
      else [qc|ExtractResult (Maybe {haskellTypeName})|]

  [qc|let !(ExtractResult {haskellAttrName} ofs{aIdx}) = {requiredModifier}extractAttribute {oldOfs} extract{haskellTypeName}Content :: {finalExtractorType} in|]

generateAttrContentExtract :: ContentWithAttrsGI -> FunctionBody
generateAttrContentExtract cgi = FunctionBody $ runCodeWriter do
  let recType = cgi.typeName
  let baseType = cgi.content.typeName.type_
  let contentField = cgi.content.haskellName
  let attrNum = length cgi.attributes
  let consName = cgi.consName
  let extrFuncName = [qc|extract{recType}Content|] :: String
  emitInline extrFuncName
  out1 [qc|{extrFuncName} ofs =|]
  withIndent1 $ do
    forM_ (zip cgi.attributes [1..attrNum]) $ \(attr, aIdx) ->
        out1 $ generateSingleAttrExtract recType attr aIdx
    out1 [qc|let !(ExtractResult {contentField} ofs{attrNum + 1}) = extract{baseType}Content ofs{attrNum} :: ExtractResult {baseType} in|]
    out1 [qc|ExtractResult {consName}\{..} ofs{attrNum + 1}|]

generateSequenceExtractFunctionBody :: SequenceGI -> FunctionBody
generateSequenceExtractFunctionBody s = FunctionBody $ runCodeWriter do
  let recType = s.typeName
  let attrNum = length s.attributes
  let extractorFuncName = [qc|extract{recType}Content|] :: String
  emitInline extractorFuncName
  out1 [qc|{extractorFuncName} ofs =|]
  withIndent1 $ do
      attrFields <- forM (zip s.attributes [1..attrNum]) $ \(attr, aIdx) -> do
        out1 $ generateSingleAttrExtract recType attr aIdx
        return attr.haskellName
      properFields <- forM (zip s.fields [(attrNum + 1)..]) $ \(fld, ofsIdx::Int) -> do
              let ofs = if ofsIdx == 1 then ("ofs"::XMLString) else [qc|ofs{ofsIdx - 1}|]
                  fieldName = fld.haskellName
                  fieldTypeName = fld.typeName.type_
                  extractor = getExtractorNameWithQuant ofs fld.inTagInfo fieldTypeName
                  extractorType = mkTypeWithCardinality True fld.inTagInfo [qc|{fieldTypeName}|]
              out1 [qc|let !(ExtractResult {fieldName} ofs{ofsIdx}) = {extractor} :: ExtractResult {extractorType} in|]
              return fieldName
      let fields = attrFields ++ properFields
          ofs' = if null fields then "ofs" else [qc|ofs{length fields}|]::XMLString
          haskellConsName = s.consName
      case fields of
          []         -> out1 [qc|ExtractResult {haskellConsName} {ofs'}|]
          [oneField] -> out1 [qc|ExtractResult ({haskellConsName} {oneField}) {ofs'}|]
          _          -> out1 [qc|ExtractResult ({haskellConsName}\{..}) {ofs'}|]

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
          q = "namespace qual: " <> show namespaceShort <> "; namespace: "
                <> show mbNamespace <> " typeName: " <> show typeName <> ":\n"
          knownQuals = "known quals: " <> show quals <> "\n"
      case mbNamespace of
        Nothing -> do
          let typeWithoutSchema = List.find ((== Namespace "") . fst) typesWithName
          case typeWithoutSchema of
            Just res -> res
            Nothing -> case typesWithName of
              [] -> error $ q <> ""
              [res] -> res
              types -> error $ knownQuals <> q <> "multiple types with name found: " <> show types

        Just namespace_ -> do
          withTypeNotFoundErr $ List.find ((== namespace_) . fst) typesWithName

  case Map.lookup typeName knownTypes_ of
    Nothing -> processSchemaNamedType quals_ namespace (mkXmlNameWN xmlType, knownSchType)
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
          -- { haskellName = error "should not be used before finalizing"
          { haskellName = HaskellFieldName "ABRA_SCHWABRA_KADABRA"
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

stripDigitsSuffix :: XMLString -> XMLString
stripDigitsSuffix x = do
  let (pref, suf) = BS.spanEnd (/= '_') x
  if
    | pref == "_" -> x
    | BS.length (getDigits suf) > BS.length (getOthers suf) -> stripDigitsSuffix $ BS.dropEnd 1 pref
    | otherwise -> x
  where
  getDigits = BS.filter isDigit
  getOthers = BS.filter (not . isDigit)

processType :: QualNamespace -> Maybe XmlNameWN -> Type -> CG TypeWithAttrs
processType quals (fmap (coerce stripDigitsSuffix) -> mbPossibleName) = \case
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
    Pattern{} -> lookupHaskellTypeBySchemaType quals base
    None -> lookupHaskellTypeBySchemaType quals base
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
{-
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
-}

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
    | Just innerTyPart <- mbFieldsExtension -> do
      typeName <- getUniqueTypeName possibleName.unXmlNameWN
      consName <- getUniqueConsName CnoRecord possibleName.unXmlNameWN
      newFieldsInfo <- mapM (processTyPart Nothing quals False []) innerTyPart
      newFields <- mapM elementToField newFieldsInfo
      pure
        (( typeName
        , GSeq $ seq_
          { typeName = typeName
          , consName = consName
          , fields = seq_.fields <> NE.toList newFields
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

  mbFieldsExtension :: Maybe (NE.NonEmpty TyPart)
  mbFieldsExtension = case mixin of
    Complex{attrs, inner} | null attrs -> case inner of
      Seq inners -> NE.nonEmpty inners
      _ -> Nothing
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
generateContentTypeParseFunc typeName = FunctionBody $ runCodeWriter $ do
  let funcName = getParserNameForType typeName
  emitInline funcName
  out1 (funcName <> " = parseString")

generateNewtypeExtractFunc :: NewtypeGI -> FunctionBody
generateNewtypeExtractFunc ngi = FunctionBody $ runCodeWriter do
  let typeName = ngi.typeName
      consName = ngi.consName
      wrappedName = ngi.wrappedType.type_
      rawFuncName = getParseRawFuncName typeName
  emitInline rawFuncName
  out1 [qc|{rawFuncName} =|]
  withIndent1 do
    out1 [qc|fmap {consName} . {getParseRawFuncName wrappedName}|]
  let extrFuncName = [qc|extract{typeName}Content|] :: String
  emitInline extrFuncName
  out1 [qc|{extrFuncName} ofs =|]
  withIndent1 do
    out1 [qc|mapExtr {consName} $ extract{wrappedName}Content ofs|]

getParseRawFuncName :: HaskellTypeName -> String
getParseRawFuncName typeName = [qc|parse{typeName}Raw|]

generateEnumExtractFunc :: EnumGI -> FunctionBody
generateEnumExtractFunc en = FunctionBody $ runCodeWriter do
  let recType = en.typeName
      funcName = getParseRawFuncName recType
  emitInline funcName
  out1 [qc|{funcName} = \case|]
  withIndent1 do
    for_ en.constrs \(xmlName, haskellCon) ->
      out1 [qc|"{xmlName}" -> pure {haskellCon}|]
    -- out1 [qc|unknown -> error $ "unknown enum value: " <> show unknown|]
    out1 [qc|unknown -> throw $ UnknownEnumValue "{recType}" unknown|]

  let extractFuncName = [qc|extract{recType}Content|] :: String
  emitInline extractFuncName
  out1 [qc|{extractFuncName} ofs =|]
  withIndent1 do
    out1 [qc|extractAndParse {getParseRawFuncName recType} ofs|]

generateListExtractFunc :: ListGI -> FunctionBody
generateListExtractFunc lgi = FunctionBody $ runCodeWriter do
  let recType = lgi.typeName
      consName = lgi.consName
      baseType = lgi.itemType
      funcName = [qc|extract{recType}Content|] :: String
  emitInline funcName
  out1 [qc|{funcName} ofs =|]
  withIndent1 do
    out1 [qc|mapExtr {consName} $ extractAndParse (traverse parse{baseType}Raw . BSC.words) ofs|]

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
    outCodeLine "{-# LANGUAGE OverloadedStrings #-}"
    outCodeLine "{-# LANGUAGE RankNTypes #-}"
    outCodeLine "{-# LANGUAGE LambdaCase #-}"
    outCodeLine "{-# LANGUAGE DeriveGeneric #-}"
    outCodeLine "{-# LANGUAGE DeriveAnyClass #-}"
    outCodeLine "{-# LANGUAGE RecordWildCards #-}"
    outCodeLine "{-# LANGUAGE ScopedTypeVariables #-}"
    outCodeLine "{-# LANGUAGE TupleSections #-}"
    outCodeLine "{-# LANGUAGE TemplateHaskell #-}"
    outCodeLine "{-# LANGUAGE NumericUnderscores #-}"
    outCodeLine "{-# LANGUAGE MagicHash #-}"
    outCodeLine "{-# LANGUAGE UnboxedTuples #-}"
    outCodeLine "{-# LANGUAGE StrictData #-}" -- implied by Strict, but anyway
    outCodeLine "{-# LANGUAGE Strict #-}"
    outCodeLine "{-# LANGUAGE BangPatterns #-}"
    outCodeLine "{-# LANGUAGE NamedFieldPuns #-}"
    outCodeLine "{-# LANGUAGE DeriveFunctor #-}"
    outCodeLine ""
    outCodeLine "module XMLSchema where"
    outCodeLine (basePrologue isUnsafe)

identity :: p -> p
identity x = x


