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
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE ViewPatterns              #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE BlockArguments #-}
-- | Here we aim to analyze the schema.
module CodeGen(GenerateOpts(..), codegen, parserCodegen) where


import           Prelude                           hiding (id, lookup)

import Data.String.Conversions
import           Control.Arrow
import           Control.Monad
import           Control.Monad                     (forM, forM_, when)
import qualified Data.ByteString.Builder           as B
import qualified Data.ByteString.Char8             as BS
import Text.Pretty.Simple
import           Data.Default                      as Def
import qualified Data.Map.Strict                   as Map
import           Data.Maybe
import qualified Data.Set                          as Set
import           Data.String
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

import           Data.Generics.Uniplate.Operations
import qualified Data.Text.Lazy.Encoding as TLE
import qualified Data.Text.Lazy as TL
import Control.Exception (evaluate)
import Debug.Trace (trace)
import GHC.Stack (HasCallStack)
import Control.Monad.Writer (Writer, MonadWriter (..), execWriter)
import Control.Monad.Reader
import Data.Bifunctor (Bifunctor(bimap))
import qualified Data.List as List
import qualified Control.Lens as Lens
import Control.Lens
import Data.Foldable (for_)
import Identifiers (normalizeFieldName, normalizeTypeName)

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

-- | Returns a pair of field name, and type code.
--   That means that type codes are in ElementName namespace, if described in-place,
--   or standard SchemaType, if referred inside ComplexType declaration.
generateElementInstance ::
  HasCallStack =>
  XMLString -> -- container name
  Element ->
  CG TyField
generateElementInstance container elt@(Element {minOccurs, maxOccurs, eName, ..}) =
    (,) <$> (TyFieldName <$> translate (ElementName, TargetFieldName) container eName)
        <*> (TyType  <$> wrapper <$> generateElementType container elt)
  where
    wrapper tyName | minOccurs==1 && maxOccurs==MaxOccurs 1 =             tyName
                   | minOccurs==0 && maxOccurs==MaxOccurs 1 = "Maybe " <> tyName
                   | otherwise                              = "["      <> tyName <> "]"
{-generateElementInstance container _ = return ( B.byteString container
                                             , "generateElementInstanceNotFullyImplemented" )-}

generateGroupType ::
  HasCallStack =>
  XMLString -> -- group name
  CG TyField
generateGroupType groupName =
    (,) <$> (TyFieldName <$> trans TargetFieldName)
        <*> (TyType      <$> trans TargetTypeName )
  where
    trans tgt = translate (SchemaGroup, tgt) groupName groupName

-- | Generate type of given <element/>, if not already declared by type="..." attribute reference.
generateElementType ::
  HasCallStack =>
  XMLString -> -- container name
  Element ->
  CG B.Builder
-- Flatten elements with known type to their types.
generateElementType _         (eType -> Ref (""    )) = return "ElementWithEmptyRefType"
generateElementType container (eType -> Ref (tyName)) =
  translate (SchemaType, TargetTypeName) container tyName
generateElementType _         (Element {eName, eType})   =
  case eType of
    Complex   {} -> generateContentType eName eType
    Extension {} -> generateContentType eName eType
    other        -> do
      warn [qc|-- Unimplemented type {other}|]
      return "Xeno.Node"

-- | Wraps type according to XML Schema "use" attribute value.
wrapAttr :: Schema.Use -> B.Builder -> B.Builder
wrapAttr  Optional   ty = "Maybe " <> ty
wrapAttr  Required   ty =             ty
wrapAttr (Default _) ty =             ty


-- | `escapeSpaces` envelop type declaration into braces if it contains spaces,
--   for example "Maybe Integer" trasforms to "(Maybe Integer)"
escapeSpaces :: TyType -> TyType
escapeSpaces ty@(TyType tyType@(builderString -> tyTypeStr))
    | BS.elem ' ' tyTypeStr = TyType $ "(" <> tyType <> ")"
    | otherwise             = ty


-- | Given a container with ComplexType details (attributes and children),
--   generate the type to hold them.
--   Or if it turns out these are referred types - just return their names.
--   That means that our container is likely 'SchemaType' namespace
generateContentType ::
  HasCallStack =>
  XMLString -- container name
                    -> Type -> CG B.Builder
generateContentType container (Ref (tyName)) = translate (SchemaType, TargetTypeName) container tyName
  -- TODO: check if the type was already translated (as it should, if it was generated)
generateContentType eName cpl@(Complex {attrs, inner}) = do
    myTypeName  <- translate (SchemaType, TargetTypeName) eName eName
    myConsName  <- translate (SchemaType, TargetConsName) eName eName
    attrFields  :: [TyField] <- tracer "attr fields"  <$> mapM makeAttrType attrs
    case inner of
        Seq ls -> do
            childFields <- seqInstance ls
            declareAlgebraicType (TyData myTypeName, [(TyCon myConsName, attrFields <> childFields)])
            return myTypeName
        All ls -> do
            -- Handling the same way as `Seq`
            generateContentType eName (cpl {inner = Seq ls})
        Choice ls -> do
            unless (null attrFields) $ warn [qc|Type {eName}: attributes in 'xs:choice' are unsupported!|]
            childFields <- choiceInstance ls
            declareSumType (TyData myTypeName, childFields)
            return myTypeName
        Elt   e     -> parseErrorBs eName $ "Unexpected singular Elt inside content of ComplexType: " <> show e
        Group gName -> parseErrorBs gName $ "Did not yet implement complexType referring only to the xs:group " <> show gName
  where
    makeAttrType :: Attr -> CG TyField
    makeAttrType Attr {..} = second (\(TyType bs) -> TyType $ wrapAttr use bs) <$> makeFieldType aName aType
    makeFieldType :: XMLString -> Type -> CG TyField
    makeFieldType  aName aType = (,) <$> (TyFieldName <$> translate (AttributeName, TargetFieldName) eName aName)
                                     <*> (TyType      <$> generateContentType                        eName aType)
    seqInstance = mapM fun
      where
        fun (Elt (elt@(Element {}))) = do
          generateElementInstance eName elt
        fun (Group gName) =
          generateGroupType gName
        fun  x =
          parseErrorBs eName [qc|Type {eName}: not yet implemented nested sequence, all or choice: {x}|]
    choiceInstance :: [TyPart] -> CG [SumAlt]
    choiceInstance ls = do
        elts <- catMaybes <$> (forM ls $ \case -- TODO move to `forM`
            Elt e -> return $ Just e
            x     -> warn [qc|Type {eName}: nested types not supported yet // {x}|] >> return Nothing)
        forM elts $ \elt@Element{eName=tName} -> do
            tyName <- translate (ChoiceIn eName, TargetConsName) eName tName
            (_, tyType) <- generateElementInstance tName elt
            return (TyCon tyName, escapeSpaces tyType)
generateContentType eName (Restriction _ (Enum (uniq -> values))) = do
  tyName     <- translate (SchemaType ,   TargetTypeName) eName        eName -- should it be split into element and type containers?
  translated <- translate (EnumIn eName,  TargetConsName) eName `mapM` values
  -- ^ TODO: consider enum as indexed family of spaces
  declareSumType (TyData tyName, (\con -> (TyCon con, TyType "")) <$> translated)
  return tyName
generateContentType eName (Restriction base (Pattern _)) = do
  tyName   <- translate (ElementName, TargetTypeName) (eName <> "pattern") base
  consName <- translate (ElementName, TargetConsName) (eName <> "pattern") base
  baseTy   <- translate (SchemaType,  TargetTypeName)  eName               base
  warn "-- Restriction pattern"
  declareNewtype (TyData tyName) (TyCon consName) (TyType baseTy)
  return tyName
generateContentType eName (Extension   base (Complex False [] (Seq []))) = do
  tyName   <- translate (SchemaType, TargetTypeName) base eName
  consName <- translate (SchemaType, TargetConsName) base eName
  baseTy   <- translate (SchemaType, TargetTypeName) base base
  declareNewtype (TyData tyName) (TyCon consName) (TyType baseTy)
  return tyName
generateContentType eName  (Restriction base  None      ) =
  -- Should we do `newtype` instead?
  generateContentType eName $ Ref base
generateContentType eName (Extension   base  (cpl@Complex {inner=Seq []})) = do
  -- TODO Unite with next code
  superTyLabel <- translate (SchemaType,TargetFieldName) eName "Super" -- should be: MetaKey instead of SchemaType
  generateContentType eName $ cpl
                  `appendElt` Element {eName=builderString superTyLabel
                                      ,eType=Ref base
                                      ,maxOccurs=MaxOccurs 1
                                      ,minOccurs=1
                                      ,targetNamespace=""}
generateContentType eName ex@(Extension _    (Complex {inner=Seq{}})) =
    getExtendedType ex >>= generateContentType eName
generateContentType eName (Extension   _base  _otherType) = do
    parseErrorBs eName [qc|Can't generate extension "{eName}"|]


getExtendedType ::
  HasCallStack =>
  Type ->
  CG Type
getExtendedType (Extension base cpl@Complex {inner=Seq {}}) = do
  -- TODO resolve right naming of superTyLabel
  superTyLabel <- builderString <$> translate (SchemaType,TargetFieldName) base "Super" -- should be: MetaKey instead of SchemaType
  return $ cpl `appendElt` Element {eName=superTyLabel
                                   ,eType=Ref base
                                   ,maxOccurs=MaxOccurs 1
                                   ,minOccurs=1
                                   ,targetNamespace=""}
getExtendedType (Extension {base}) = parseErrorBs base "Extension not yet implemented"
getExtendedType _                  = error "'getExtendedType' is available only for Extension"


appendElt :: Type -> Element -> Type
appendElt cpl@Complex { inner=Seq sq } elt  = cpl { inner=Seq (Elt elt:sq   ) }
appendElt cpl@Complex { inner=other  } elt  = cpl { inner=Seq [Elt elt,other] }
appendElt other                        _elt = error [qc|Cannot append field for supertype to: {other}|]


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


-- | Make builder to generate schema code
-- TODO rename it!
codegen    :: GenerateOpts -> Schema -> IO String
codegen opts sch = codegen' sch (generateSchema opts sch)


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
      generateParser2 opts sch
      pure ()


-- | Generate content type, and put an type name on it.
generateNamedContentType ::
  HasCallStack =>
  (XMLString, Type) ->
  CG ()
generateNamedContentType (name, ty) = do
  contentTypeName <- translate (SchemaType, TargetTypeName) name name
  contentConsName <- translate (SchemaType, TargetConsName) name name
  contentTypeCode <- generateContentType name ty
  when (isBaseHaskellType $ builderString contentTypeCode) $ do
    warn "-- Named base type"
    declareNewtype (TyData contentTypeName) (TyCon contentConsName) (TyType contentTypeCode)

generateSchema ::
  HasCallStack =>
  GenerateOpts ->
  Schema ->
  CG ()
generateSchema GenerateOpts{..} sch = do
    unless isUnsafe $ outCodeLine "{-# LANGUAGE Safe #-}"
    outCodeLine "{-# LANGUAGE DuplicateRecordFields #-}"
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
    -- First generate all types that may be referred by others.
    mapM_ generateNamedContentType $ Map.toList $ types sch
    -- Then generate possible top level types.
    topElementTypeNames <- generateElementType "Top" `mapM` tops sch
    case topElementTypeNames of
      []                                          -> fail "No toplevel elements found!"
      [eltName]
        | isBaseHaskellType (builderString eltName) -> do
           outCodeLine "-- Toplevel"
           declareNewtype (TyData topLevelConst) (TyCon topLevelConst) (TyType eltName)
      [eltName]                                   -> do
           -- TODO change to Template Haskell generation
           outCodeLine [qc|type {topLevelConst::String} = {eltName}|]
      altTypes                                    -> do
           -- Add constructor name for each type
           -- TODO: We would gain from separate dictionary for constructor names!
           alts <- (map (TyCon *** TyType)) <$>
                   (`zip` altTypes) <$>
                       forM altTypes
                            (translate (SchemaType, TargetTypeName) topLevelConst . builderString)
           declareSumType (TyData topLevelConst, alts)
    pure ()
    declareAlgebraicType $ mkSequenceTypeDeclaration exampleSequenceGI
    generateFunction $ generateSequenceParseFunctionBody exampleSequenceGI
    generateFunction $ generateSequenceExtractFunctionBody exampleSequenceGI
    pure ()


topLevelConst :: IsString a => a
topLevelConst = "TopLevel"

-- | Eliminate duplicates from the list
-- TODO use from library
uniq :: Ord a => [a] -> [a]
uniq  = Set.toList . Set.fromList

-- * Debugging
tracer :: String -> p2 -> p2
--tracer lbl a = trace (lbl <> show a) a
tracer _ a = a


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

generateParser1 :: GenerateOpts -> Schema -> CG ()
generateParser1 opts@GenerateOpts{..} schema = do
    -- pTraceShowM schema
    generateSchema opts schema
    outCodeLine [qc|-- PARSER --|]
    generateParserInternalStructures
    generateParserInternalArray opts schema
    outCodeLine ""
    outCodeLine ""
    outCodeLine "-- extr --"
    outCodeLine ""
    outCodeLine ""
    generateParserExtractTopLevel opts schema
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


data Repeatedness = RepMaybe
                  | RepOnce
                  | RepMany
                  | RepNotLess Int
                  | RepRange Int Int
                  deriving Show


eltToRepeatedness :: Element -> Repeatedness
eltToRepeatedness (Element 0 Unbounded     _ _ _) = RepMany
eltToRepeatedness (Element 0 (MaxOccurs 1) _ _ _) = RepMaybe
eltToRepeatedness (Element 0 _             _ _ _) = RepMany
eltToRepeatedness (Element 1 (MaxOccurs 1) _ _ _) = RepOnce
eltToRepeatedness (Element 1 _             _ _ _) = RepMany
eltToRepeatedness (Element m Unbounded     _ _ _) = RepNotLess m
eltToRepeatedness (Element m (MaxOccurs n) _ _ _) = RepRange m n


-- TODO use `baseTranslations`
getParserForStandardXsd :: XMLString -> Maybe XMLString
getParserForStandardXsd "xs:integer"            = Just "Integer"
getParserForStandardXsd "xs:int"                = Just "Int"
getParserForStandardXsd "xs:byte"               = Just "Integer"
getParserForStandardXsd "xs:long"               = Just "Int64"
getParserForStandardXsd "xs:negativeInteger"    = Just "Integer"
getParserForStandardXsd "xs:nonNegativeInteger" = Just "Integer"
getParserForStandardXsd "xs:positiveInteger"    = Just "Integer"
getParserForStandardXsd "xs:nonPositiveInteger" = Just "Integer"
getParserForStandardXsd "xs:short"              = Just "Integer"
getParserForStandardXsd "xs:unsignedLong"       = Just "Integer"
getParserForStandardXsd "xs:unsignedInt"        = Just "Integer"
getParserForStandardXsd "xs:unsignedShort"      = Just "Integer"
getParserForStandardXsd "xs:unsignedByte"       = Just "Integer"
getParserForStandardXsd "xs:stringContent"      = Just "String"
getParserForStandardXsd "xs:decimal"            = Just "Decimal"
getParserForStandardXsd "xs:string"             = Just "String"
getParserForStandardXsd "xs:token"              = Just "String"
getParserForStandardXsd "xs:date"               = Just "Day"
getParserForStandardXsd "xs:duration"           = Just "Duration" -- TODO
getParserForStandardXsd "xs:dateTime"           = Just "DateTime"
getParserForStandardXsd "xs:gYearMonth"         = Just "Day"
getParserForStandardXsd "xs:gMonth"             = Just "Day"
getParserForStandardXsd "xs:gYear"              = Just "Day"
getParserForStandardXsd "xs:boolean"            = Just "Boolean"
getParserForStandardXsd "xs:anyURI"             = Just "String" -- TODO
getParserForStandardXsd "xs:any"                = Just "String" -- TODO: what is xs:any? Can it be String?
getParserForStandardXsd _                       = Nothing


-- | Retrieve all schema types (even not declared on top level)
--   in order to generate parsers for each of them.
--
--   First are returned types declared on top schema level, then other types.
extractAllTypes :: TypeDict -> [Element] -> [(XMLString, Type)]
extractAllTypes types tops =
    removeDuplicatesInFavourOfFirst $ typeList ++ referencedTypes
  where
    typeList = Map.toList types
    allElts = universeBi typeList ++ universeBi tops
    referencedTypes = map (\(Element _ _ name typ _) -> (name, typ)) allElts
    removeDuplicatesInFavourOfFirst = Map.toList . Map.fromList . reverse


generateParserInternalArray :: GenerateOpts -> Schema -> CG ()
generateParserInternalArray GenerateOpts{..} Schema{tops, types} = do
    outCodeLine [qc|-- PARSER --|]
    -- FIXME: examine which element is on the toplevel, if there are many
    when (length tops /= 1) $ error "Only one element supported on toplevel."
    let topEl = head tops
    -- Generate parser header
    let topName = eName topEl
    when (minOccurs topEl /= 1) $ parseErrorBs topName [qc|Wrong minOccurs = {minOccurs topEl}|]
    when (maxOccurs topEl /= MaxOccurs 1) $ parseErrorBs topName [qc|Wrong maxOccurs = {maxOccurs topEl}|]
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
                outCodeLine' [qc|(_, _) <- inOneTag "{topName}" (skipSpaces $ skipHeader $ skipSpaces 0) $ parse{topName}Content 0|]
                outCodeLine' [qc|return ()|]
                outCodeLine' [qc|where|]
                withIndent $ do
                    -- Generate parsers for certain types
                    let types' = extractAllTypes types tops
                    forM_ types' $ \(typeName, ty) -> do
                        outCodeLine' [qc|parse{typeName}Content arrStart strStart = do|]
                        withIndent $ generateContentParserIA typeName ty
                    -- Generate auxiliary functions
                    generateAuxiliaryFunctionsIA
        outCodeLine' [qc|parse{topName} vec|]
        outCodeLine' [qc|return vec|]
  where
    generateElementsOfComplexParser :: (XMLString, XMLString) -> [TyPart] -> CG (XMLString, XMLString)
    generateElementsOfComplexParser (arrStart, strStart) typarts = do
        let ofsNames' = ((arrStart, strStart) : [ ( [qc|arrOfs{i}|], [qc|strOfs{i}|]) | i <- [(1::Int)..]])
                        :: [(XMLString, XMLString)]
            ofsNames = zip ofsNames' (tail ofsNames')
            endNum = length typarts
        forM_ (zip ofsNames typarts) $ \(((arrOfs, strOfs), (arrOfs', strOfs')), typart) -> do
            case typart of
                Elt el -> do
                    let parserName = getParserName (eType el) (eName el)
                        (isUseArrOfs, tagQuantifier::XMLString) = case eltToRepeatedness el of
                            RepMaybe -> (True,  "inMaybeTag")
                            RepOnce  -> (False, "inOneTag")
                            _        -> (True,  "inManyTags")
                        (arrOfs1, arrOfs2)::(XMLString,XMLString) =
                            if isUseArrOfs then ([qc| {arrOfs}|],"") else ("", [qc| {arrOfs}|])
                    -- TODO parse with attributes!
                    outCodeLine' [qc|({arrOfs'}, {strOfs'}) <- {tagQuantifier} "{eName el}"{arrOfs1} {strOfs} $ parse{parserName}{arrOfs2}|]
                Group gName ->
                    outCodeLine' [qc|({arrOfs'}, {strOfs'}) <- parse{gName}Content {arrOfs} {strOfs}|]
                _ -> parseErrorBs arrStart [qc|Unsupported type: {take 100 $ show typart}|]
        return $ fst $ ofsNames !! endNum
    ofsToReturn :: (XMLString, XMLString) -> CG ()
    ofsToReturn (arrLastOfs, strLastOfs) = outCodeLine' [qc|return ({arrLastOfs}, {strLastOfs})|]
    generateContentParserIA typeName ty = do
        case ty of
            Complex _ _attrs (Seq elts) -> do
                generateElementsOfComplexParser ("arrStart", "strStart") elts >>= ofsToReturn
            c@(Complex _ _attrs (Choice choices)) -> do
                -- outCodeLine' [qc|-- Complex: {c}|]
                outCodeLine' [qc|let arrOfs' = arrStart + 1|]
                outCodeLine' [qc|case (getTagName strStart) of|]
                withIndent $ do
                    -- TODO what to do if there are two options with minOccurs="0" ?
                    forM_ (zip choices [0..]) $ \case
                        (Elt e, i) -> do
                            outCodeLine' [qc|"{eName e}" -> do|]
                            withIndent $ do
                                (a,o) <- generateElementsOfComplexParser ("arrOfs'", "strStart") [Elt e]
                                outCodeLine' [qc|{vecWrite} vec arrStart {i::Int}|]
                                outCodeLine' [qc|return ({a}, {o})|]
                        (x, _) -> warn [qc|Type {c}: nested types not supported yet // {x}|]
            r@(Ref {}) -> do
                let parserName = getParserName r ""
                outCodeLine' [qc|parse{parserName} arrStart strStart -- !! <{typeName}> / <{ty}>|]
            Restriction _ _ ->
                outCodeLine' [qc|parseString arrStart strStart|]
            Extension base (Complex {inner=Seq exFields}) -> do
                let baseParserName = fromMaybe [qc|{base}Content|] $ getParserForStandardXsd base
                outCodeLine' [qc|(arrOfs', strOfs') <- parse{baseParserName} arrStart strStart|]
                generateElementsOfComplexParser ("arrOfs'", "strOfs'") exFields >>= ofsToReturn
            _ -> parseErrorBs typeName [qc|Unsupported type: {ty}|]
    -- TODO unite with extractor
    getParserName :: Type -> XMLString -> XMLString
    getParserName (Ref r) _ =
        case getParserForStandardXsd r of
            Nothing ->
                if "xs:" `BS.isPrefixOf` r
                then parseErrorBs r [qc|Standard type `{r}` is not supported|]
                else [qc|{r}Content|]
            Just rr -> rr
    getParserName (Complex {}) xname     = [qc|{xname}Content|]
    getParserName (Extension {base}) xname =
        fromMaybe [qc|{xname}Content|] $ getParserForStandardXsd base
    getParserName t _                    = [qc|???{t}|]
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
        outCodeLine' [qc|inOneTag          tag strOfs inParser = toError tag strOfs $ inOneTag' True tag strOfs inParser|] -- TODO add attributes processing
        outCodeLine' [qc|inOneTagWithAttrs tag strOfs inParser = toError tag strOfs $ inOneTag' True  tag strOfs inParser|]
        outCodeLine' [qc|inOneTag' hasAttrs tag strOfs inParser = do|]
        outCodeLine' [qc|    let tagOfs = skipToOpenTag strOfs + 1|]
        outCodeLine' [qc|    case ensureTag hasAttrs tag tagOfs of|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag tagOfs|]
        outCodeLine' [qc|            return Nothing|]
        outCodeLine' [qc|        Just (ofs', True) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser (ofs' - 1)|] -- TODO points to special unparseable place
        outCodeLine' [qc|            return $ Just (arrOfs, ofs')|]
        outCodeLine' [qc|        Just (ofs', _) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser ofs'|]
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
        outCodeLine' [qc|inMaybeTag tag arrOfs strOfs inParser = inMaybeTag' True tag arrOfs strOfs inParser|] -- TODO add attributes processing
        --outCodeLine' [qc|inMaybeTag' :: Bool -> ByteString -> Int -> Int -> (Int -> Int -> ST s (Int, Int)) -> ST s (Int, Int)|]
        outCodeLine' [qc|inMaybeTag' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    inOneTag' hasAttrs tag strOfs (inParser arrOfs) >>= \case|]
        outCodeLine' [qc|        Just res -> return res|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag strOfs|]
        outCodeLine' [qc|            {vecWrite} vec arrOfs 0|]
        outCodeLine' [qc|            {vecWrite} vec (arrOfs + 1) 0|]
        outCodeLine' [qc|            return (arrOfs + 2, strOfs)|]
        outCodeLine' [qc|inManyTags tag arrOfs strOfs inParser = inManyTags' True tag arrOfs strOfs inParser|] -- TODO add attributes processing
        outCodeLine' [qc|inManyTagsWithAttrs tag arrOfs strOfs inParser = inManyTags' True tag arrOfs strOfs inParser|]
        --outCodeLine' [qc|inManyTags' :: Bool -> ByteString -> Int -> Int -> (Int -> Int -> ST s (Int, Int)) -> ST s (Int, Int)|]
        outCodeLine' [qc|inManyTags' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    (cnt, endArrOfs, endStrOfs) <- flip fix (0, (arrOfs + 1), strOfs) $ \next (cnt, arrOfs', strOfs') ->|]
        outCodeLine' [qc|        inOneTag' hasAttrs tag strOfs' (inParser arrOfs') >>= \case|]
        outCodeLine' [qc|            Just (arrOfs'', strOfs'') -> next   (cnt + 1, arrOfs'', strOfs'')|]
        outCodeLine' [qc|            Nothing                   -> do|]
        outCodeLine' [qc|                updateFarthest tag strOfs|]
        outCodeLine' [qc|                return (cnt,     arrOfs', strOfs')|]
        outCodeLine' [qc|    {vecWrite} vec arrOfs cnt|]
        outCodeLine' [qc|    return (endArrOfs, endStrOfs)|]
        -- ~~~~~~~~
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
        outCodeLine' [qc|parseString arrStart strStart = do|]
        outCodeLine' [qc|  let strEnd = skipToOpenTag strStart|]
        outCodeLine' [qc|  {vecWrite} vec arrStart     strStart|]
        outCodeLine' [qc|  {vecWrite} vec (arrStart+1) (strEnd - strStart)|]
        outCodeLine' [qc|  return (arrStart+2, strEnd)|]
        outCodeLine' [qc|parseDecimal = parseString|]
        outCodeLine' [qc|parseDateTime = parseString|]
        outCodeLine' [qc|parseDuration = parseString|]
        outCodeLine' [qc|parseInteger = parseString|]
        outCodeLine' [qc|parseInt = parseString|]
        outCodeLine' [qc|parseInt64 = parseString|]
        outCodeLine' [qc|parseDay = parseString|]
        outCodeLine' [qc|parseBool = parseString|]
        outCodeLine' [qc|skipSpaces ofs|]
        outCodeLine' [qc|  | isSpaceChar (bs `{bsIndex}` ofs) = skipSpaces (ofs + 1)|]
        outCodeLine' [qc|  | otherwise = ofs|]
        outCodeLine' [qc|isSpaceChar :: Word8 -> Bool|]
        outCodeLine' [qc|isSpaceChar c = c == 32 || c == 10 || c == 9 || c == 13|]
        outCodeLine' [qc|skipHeader :: Int -> Int|]
        outCodeLine' [qc|skipHeader ofs|]
        outCodeLine' [qc|  | bs `{bsIndex}` ofs == openTagChar && bs `{bsIndex}` (ofs + 1) == questionChar = skipToCloseTag (ofs + 2) + 1|]
        outCodeLine' [qc|  | otherwise = ofs|]
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


generateParserExtractTopLevel ::
  HasCallStack =>
  GenerateOpts ->
  Schema ->
  CG ()
generateParserExtractTopLevel GenerateOpts{..} Schema{..} = do
    forM_ tops $ \topEl -> do
        let rootName = eName topEl
        haskellRootName :: B.Builder <- translate (ElementName, TargetTypeName) "" rootName -- TODO container?
        outCodeLine' [qc|extractTopLevel :: TopLevelInternal -> TopLevel|]
        outCodeLine' [qc|extractTopLevel (TopLevelInternal bs arr) = fst $ extract{haskellRootName}Content 0|]
    withIndent $ do
        outCodeLine' "where"
        let types' = extractAllTypes types tops
        withIndent $ do
            forM_ types' $ \(typeName, ty) -> do
            -- forM_ (take 1 ((Map.toList types) ++ additionalTypes)) $ \(typeName, ty) -> do
                -- OK: haskellTypeName <- translate (SchemaType, TargetTypeName) typeName typeName -- TODO container?
                haskellTypeName <- translate (ElementName, TargetTypeName) typeName typeName -- TODO container?
                --pTraceM [qc|Extractor: typeName = <{typeName}>|]
                --pTraceM [qc|Extractor: ty = <{take 150 $ show ty}>|]
                --pTraceM [qc|Extractor: haskellTypeName = <{haskellTypeName}>|]
                outCodeLine' [qc|extract{haskellTypeName}Content ofs =|]
                withIndent $ generateContentParser typeName haskellTypeName ty
            generateAuxiliaryFunctions
  where
    getExtractorNameWithQuant :: XMLString -> Element -> CG XMLString -- ? Builder
    getExtractorNameWithQuant ofs el = do
        extractorName <- getExtractorName (eType el) (eName el)
        let (fieldQuantifier::(Maybe XMLString)) = case eltToRepeatedness el of
                RepMaybe -> Just "extractMaybe"
                RepOnce  -> Nothing
                _        -> Just "extractMany" -- TODO add extractExact support
        return $ case fieldQuantifier of
                 Nothing   -> [qc|extract{extractorName}Content {ofs}|]
                 Just qntf -> [qc|{qntf} {ofs} extract{extractorName}Content|]
    generateContentParser typeName haskellTypeName ty =
        case ty of
            Complex _ attrs (Seq elts) ->
                withIndent $ do
                    attrFields <- forM attrs $ \attr -> do
                        let aname = aName attr
                        haskellAttrName <- translate (AttributeName, TargetFieldName) aname aname -- TODO container?
                        outCodeLine' [qc|let {haskellAttrName} = Nothing in|]
                        return haskellAttrName
                    properFields <- forM (zip elts [1..]) $ \case
                        (Elt el, ofsIdx::Int) -> do
                            let ofs = if ofsIdx == 1 then ("ofs"::XMLString) else [qc|ofs{ofsIdx - 1}|]
                                fieldName' = eName el
                            extractor <- getExtractorNameWithQuant ofs el
                            fieldName <- translate (ElementName, TargetFieldName) fieldName' fieldName' -- TODO container?
                            outCodeLine' [qc|let ({fieldName}, ofs{ofsIdx}) = {extractor} in|]
                            return fieldName
                        (Group gName, ofsIdx) -> do
                            outCodeLine' [qc|-- Group: {gName}|]
                            extractor <- translate (SchemaGroup, TargetConsName) gName gName
                            fieldName <- translate (SchemaGroup, TargetFieldName) gName gName -- TODO container?
                            outCodeLine' [qc|let ({fieldName}, ofs{ofsIdx}) = extract{extractor}Content ofs{ofsIdx - 1} in|]
                            return fieldName
                        _ -> parseErrorBs typeName [qc|Unsupported type: {take 100 $ show ty}|]
                    let fields = attrFields ++ properFields
                        ofs' = if null elts then "ofs" else [qc|ofs{length elts}|]::XMLString
                    haskellConsName <- translate (SchemaType, TargetConsName) typeName typeName -- TODO container?
                    case fields of
                        []         -> outCodeLine' [qc|({haskellConsName}, {ofs'})|]
                        [oneField] -> outCodeLine' [qc|({haskellConsName} {oneField}, {ofs'})|]
                        _          -> outCodeLine' [qc|({haskellConsName}\{..}, {ofs'})|]
            r@(Ref {}) -> do
                rname <- getExtractorName r ""
                outCodeLine' [qc|extract{rname}Content ofs|]
            Restriction _ (Enum opts) -> do
                outCodeLine' [qc|first (\case|]
                withIndent $ do
                    forM_ (uniq opts) $ \opt -> do
                        tn <- translate (EnumIn typeName, TargetConsName) typeName opt -- TODO change 'typeName' to 'haskellTypeName' ?
                        outCodeLine' [qc|"{opt}" -> {tn}|]
                    outCodeLine' [qc|) $ extractStringContent ofs|]
            Restriction baseType _ -> do
                postProcess <- if baseType == "xs:string" || baseType == "xs:token"
                               then do
                                   haskellConsName <- translate (SchemaType, TargetConsName) typeName typeName -- TODO container?
                                   return [qc|first {haskellConsName} $ |]
                               else return (""::XMLString)
                outCodeLine' [qc|{postProcess}extractStringContent ofs|]
            e@(Extension _ _) -> do
                getExtendedType e >>= generateContentParser typeName haskellTypeName
            c@(Complex _ _attrs (Choice choices)) -> do
                outCodeLine' [qc|let ofs' = ofs + 1 in|]
                outCodeLine' [qc|case (arr {index} ofs) of|]
                withIndent $ do
                    -- TODO what to do if there are two options with minOccurs="0" ?
                    forM_ (zip choices [0..]) $ \case
                        (Elt el, i) -> do
                            extractor <- getExtractorNameWithQuant "ofs'" el
                            tn <- translate (ChoiceIn typeName, TargetConsName) typeName (eName el) -- TODO change 'typeName' to 'haskellTypeName' ?
                            outCodeLine' [qc|{i::Int} -> first {tn} $ {extractor}|]
                        (x, _) -> warn [qc|Type {c}: nested types not supported yet // {x}|]
            _ -> parseErrorBs typeName [qc|Unsupported type: {show ty}|]
    getExtractorName :: Type -> XMLString -> CG B.Builder
    getExtractorName (Ref r) _ =
        case getParserForStandardXsd r of
            Nothing ->
                if "xs:" `BS.isPrefixOf` r
                then error [qc|Standard type `{r}` is not supported|]
                else translate (ElementName, TargetTypeName) r r -- TODO container?
            Just rr -> return $ B.byteString rr
    getExtractorName (Complex {}) xname   = translate (ElementName, TargetTypeName) xname xname
    getExtractorName (Extension {}) xname = translate (ElementName, TargetTypeName) xname xname
    getExtractorName t _                  = error [qc|Don't know how to generate {take 100 $ show t}|]
    generateAuxiliaryFunctions = do
        outCodeLine' [qc|extractStringContent :: Int -> (ByteString, Int)|]
        if isUnsafe then
            outCodeLine' [qc|extractStringContent ofs = (BSU.unsafeTake bslen (BSU.unsafeDrop bsofs bs), ofs + 2)|]
        else
            outCodeLine' [qc|extractStringContent ofs = (BS.take bslen (BS.drop bsofs bs), ofs + 2)|]
        outCodeLine' [qc|  where|]
        outCodeLine' [qc|    bsofs = arr {index} ofs|]
        outCodeLine' [qc|    bslen = arr {index} (ofs + 1)|]
        outCodeLine' [qc|extractMaybe ofs subextr|]
        outCodeLine' [qc|  | arr {index} ofs == 0 = (Nothing, ofs + 2)|]
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
        outCodeLine' [qc|extractDecimalContent :: Int -> (Scientific, Int)|]
        outCodeLine' [qc|extractDecimalContent = extractReadInst|]
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

-- GI stands for "generating input"
-- type for processing sequence inside complexType
data SequenceGI = SequenceGI
  { typeName :: HaskellTypeName
  , consName :: HaskellConsName
  , attributes :: [FieldGI]
  , fields :: [FieldGI]
  }

data FieldGI = FieldGI
  { haskellName :: HaskellFieldName
  , xmlName :: XMLString
  , cardinality :: Repeatedness
  , typeName :: HaskellTypeName
  }

mkSequenceTypeDeclaration :: SequenceGI -> (TyData, [Record])
mkSequenceTypeDeclaration s =
  (TyData $ B.byteString s.typeName.unHaskellTypeName
  , [(TyCon $ B.byteString s.consName.unHaskellConsName, map mkFieldDeclaration $ s.attributes <> s.fields)]
  )

mkFieldDeclaration :: FieldGI -> TyField
mkFieldDeclaration fld =
  ( TyFieldName $ B.byteString fld.haskellName.unHaskellFieldName
  , TyType $ mkCardinality $ B.byteString fld.typeName.unHaskellTypeName
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
    [ FieldGI "departure" "departureElt" RepMaybe "String"
    , FieldGI "arrival" "arrivalElt" RepOnce "Int"
    , FieldGI "techStops" "techStopsElt" RepMany "TechStop"
    ]
  }

type CodeWriter = ReaderT Int (Writer [String]) ()

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

generateSequenceParseFunctionBody :: SequenceGI -> FunctionBody
generateSequenceParseFunctionBody s = FunctionBody $ runCodeWriter $
  out1 (getParserNameForType s.typeName <> " arrStart strStart = do") >> withIndent1 do
    let (arrStart, strStart) = ("arrStart", "strStart")
        fields = {- s.attributes <> -} s.fields
    let ofsNames' = ((arrStart, strStart) : [ ( [qc|arrOfs{i}|], [qc|strOfs{i}|]) | i <- [(1::Int)..]])
                    :: [(XMLString, XMLString)]
        ofsNames = zip ofsNames' (tail ofsNames')
        (arrRet, strRet) = bimap bld bld $ ofsNames' !! length fields
    forM_ (zip ofsNames fields) $ \(((arrOfs, strOfs), (arrOfs', strOfs')), field) -> do
      let parserName = getParserNameForType field.typeName
      let (isUseArrOfs, tagQuantifier::XMLString) = case field.cardinality of
              RepMaybe -> (True,  "inMaybeTag")
              RepOnce  -> (False, "inOneTag")
              _        -> (True,  "inManyTags")
          (arrOfs1, arrOfs2)::(XMLString,XMLString) =
              if isUseArrOfs then ([qc| {arrOfs}|],"") else ("", [qc| {arrOfs}|])
          tagName = field.xmlName
      -- TODO parse with attributes!
      out1 [qc|({arrOfs'}, {strOfs'}) <- {tagQuantifier} "{tagName}"{arrOfs1} {strOfs} $ {parserName}{arrOfs2}|]
    out1 [qc|pure ({arrRet}, {strRet})|]



generateSequenceExtractFunctionBody :: SequenceGI -> FunctionBody
generateSequenceExtractFunctionBody s = FunctionBody $ runCodeWriter do
  let recType = bld s.typeName.unHaskellTypeName
  out1 [qc|extract{recType}Content ofs =|]
  withIndent1 $ do
      attrFields <- forM s.attributes $ \attr -> do
          let haskellAttrName = attr.haskellName.unHaskellFieldName
          out1 [qc|let {bld haskellAttrName} = Nothing in|]
          return haskellAttrName
      properFields <- forM (zip s.fields [1..]) $ \(fld, ofsIdx::Int) -> do
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
            fieldTypeName = bld fld.typeName.unHaskellTypeName
        case fieldQuantifier of
                 Nothing   -> [qc|extract{fieldTypeName}Content {ofs}|]
                 Just qntf -> [qc|{qntf} {ofs} extract{fieldTypeName}Content|]

lookupHaskellTypeBySchemaType :: XMLString -> CG HaskellTypeName
lookupHaskellTypeBySchemaType xmlType = do
  knownTypes_ <- Lens.use knownTypes
  pure $ fromMaybe (error "unknown type") $ Map.lookup xmlType knownTypes_

registerDataDeclaration :: (TyData, [Record]) -> CG ()
registerDataDeclaration decl = typeDecls %= (decl :)

registerExtractionFunction :: FunctionBody -> CG ()
registerExtractionFunction fBody = extractFunctions %= (fBody :)

registerParseFunction :: FunctionBody -> CG ()
registerParseFunction fBody = parseFunctions %= (fBody :)

registerSequenceGI :: SequenceGI -> CG ()
registerSequenceGI s = do
  registerDataDeclaration $ mkSequenceTypeDeclaration s
  registerExtractionFunction $ generateSequenceExtractFunctionBody s
  registerParseFunction $ generateSequenceParseFunctionBody s

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
getUniqueTypeName s =
  getUniqueName mkHaskellTypeName s getAllocatedHaskellTypes

getUniqueConsName :: XMLString -> CG HaskellConsName
getUniqueConsName s = getUniqueName mkHaskellConsName s getAllocatedHaskellConstructors

processComplex ::
  XMLString -> -- ^ possible name
  Bool ->
  [Attr] ->
  TyPart ->
  CG HaskellTypeName
processComplex (normalizeTypeName -> possibleName) _mixed attrs inner = case inner of
  Seq seqParts -> case traverse getElement seqParts of
    Nothing -> error "only sequence of elements is supported"
    Just elts -> do
      sGI <- mkSequenceGI elts
      registerSequenceGI sGI
      pure sGI.typeName
  _ -> error "anything other than Seq inside Complex is not supported"
  where
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
  attributeToField :: Attr -> CG FieldGI
  attributeToField attr = do
    typeName <- processType (aName attr) $ aType attr
    pure FieldGI
      { haskellName = attrNameToHaskellFieldName $ aName attr
      , xmlName = aName attr
      , cardinality = RepMaybe
      , typeName
      }
  elementToField :: Element -> CG FieldGI
  elementToField elt = do
    typeName <- processType (eName elt) $ eType elt
    pure FieldGI
      { haskellName = eltNameToHaskellFieldName $ eName elt
      , xmlName = eName elt
      , cardinality = getCardinality elt
      , typeName
      }
  getCardinality elt = case (minOccurs elt, maxOccurs elt) of
    (1, MaxOccurs 1) -> RepOnce
    (0, MaxOccurs 1) -> RepMaybe
    (_, _) -> RepMany
  getElement :: TyPart -> Maybe Element
  getElement (Elt e) = Just e
  getElement _ = Nothing

eltNameToHaskellFieldName :: BS.ByteString -> HaskellFieldName
eltNameToHaskellFieldName = HaskellFieldName . normalizeFieldName

attrNameToHaskellFieldName :: XMLString -> HaskellFieldName
attrNameToHaskellFieldName = HaskellFieldName . normalizeFieldName

processType :: XMLString -> Type -> CG HaskellTypeName
processType (normalizeTypeName -> possibleName) = \case
  Ref knownType ->
    lookupHaskellTypeBySchemaType knownType
  Complex{mixed, attrs, inner} ->
    processComplex possibleName mixed attrs inner
  _ -> error "not ref and complex, not supported"

registerNamedType :: XMLString -> HaskellTypeName -> CG ()
registerNamedType xmlName haskellType = knownTypes %= Map.insert xmlName haskellType

processSchemaNamedTypes :: TypeDict -> CG ()
processSchemaNamedTypes dict = forM_ (Map.toList dict) \(tName, tDef) -> do
  haskellTypeName <- processType tName tDef
  registerNamedType tName haskellTypeName

generateParser2 :: GenerateOpts -> Schema -> CG ()
generateParser2 opts@GenerateOpts{isGenerateMainFunction} schema = do
    generateModuleHeading opts
    processSchemaNamedTypes schema.types
    topNames <- forM schema.tops \el -> processType (eName el) (eType el)
    declaredTypes <- Lens.use typeDecls
    outCodeLine [qc|type TopLevel = {bld $ unHaskellTypeName $ head topNames}|]
    mapM_ declareAlgebraicType declaredTypes
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

generateParserInternalArray1 :: GenerateOpts -> Schema -> CG ()
generateParserInternalArray1 GenerateOpts{isUnsafe} Schema{tops} = do
    outCodeLine [qc|-- PARSER --|]
    -- FIXME: examine which element is on the toplevel, if there are many
    when (length tops /= 1) $ error "Only one element supported on toplevel."
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
                outCodeLine' [qc|(_, _) <- inOneTag "{topTag}" (skipSpaces $ skipHeader $ skipSpaces 0) $ parse{topName}Content 0|]
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
        outCodeLine' [qc|inOneTag          tag strOfs inParser = toError tag strOfs $ inOneTag' True tag strOfs inParser|] -- TODO add attributes processing
        outCodeLine' [qc|inOneTagWithAttrs tag strOfs inParser = toError tag strOfs $ inOneTag' True  tag strOfs inParser|]
        outCodeLine' [qc|inOneTag' hasAttrs tag strOfs inParser = do|]
        outCodeLine' [qc|    let tagOfs = skipToOpenTag strOfs + 1|]
        outCodeLine' [qc|    case ensureTag hasAttrs tag tagOfs of|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag tagOfs|]
        outCodeLine' [qc|            return Nothing|]
        outCodeLine' [qc|        Just (ofs', True) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser (ofs' - 1)|] -- TODO points to special unparseable place
        outCodeLine' [qc|            return $ Just (arrOfs, ofs')|]
        outCodeLine' [qc|        Just (ofs', _) -> do|]
        outCodeLine' [qc|            (arrOfs, strOfs) <- inParser ofs'|]
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
        outCodeLine' [qc|inMaybeTag tag arrOfs strOfs inParser = inMaybeTag' True tag arrOfs strOfs inParser|] -- TODO add attributes processing
        --outCodeLine' [qc|inMaybeTag' :: Bool -> ByteString -> Int -> Int -> (Int -> Int -> ST s (Int, Int)) -> ST s (Int, Int)|]
        outCodeLine' [qc|inMaybeTag' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    inOneTag' hasAttrs tag strOfs (inParser arrOfs) >>= \case|]
        outCodeLine' [qc|        Just res -> return res|]
        outCodeLine' [qc|        Nothing -> do|]
        outCodeLine' [qc|            updateFarthest tag strOfs|]
        outCodeLine' [qc|            {vecWrite} vec arrOfs 0|]
        outCodeLine' [qc|            {vecWrite} vec (arrOfs + 1) 0|]
        outCodeLine' [qc|            return (arrOfs + 2, strOfs)|]
        outCodeLine' [qc|inManyTags tag arrOfs strOfs inParser = inManyTags' True tag arrOfs strOfs inParser|] -- TODO add attributes processing
        outCodeLine' [qc|inManyTagsWithAttrs tag arrOfs strOfs inParser = inManyTags' True tag arrOfs strOfs inParser|]
        --outCodeLine' [qc|inManyTags' :: Bool -> ByteString -> Int -> Int -> (Int -> Int -> ST s (Int, Int)) -> ST s (Int, Int)|]
        outCodeLine' [qc|inManyTags' hasAttrs tag arrOfs strOfs inParser = do|]
        outCodeLine' [qc|    (cnt, endArrOfs, endStrOfs) <- flip fix (0, (arrOfs + 1), strOfs) $ \next (cnt, arrOfs', strOfs') ->|]
        outCodeLine' [qc|        inOneTag' hasAttrs tag strOfs' (inParser arrOfs') >>= \case|]
        outCodeLine' [qc|            Just (arrOfs'', strOfs'') -> next   (cnt + 1, arrOfs'', strOfs'')|]
        outCodeLine' [qc|            Nothing                   -> do|]
        outCodeLine' [qc|                updateFarthest tag strOfs|]
        outCodeLine' [qc|                return (cnt,     arrOfs', strOfs')|]
        outCodeLine' [qc|    {vecWrite} vec arrOfs cnt|]
        outCodeLine' [qc|    return (endArrOfs, endStrOfs)|]
        -- ~~~~~~~~
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

generateParserExtractTopLevel1 ::
  HasCallStack =>
  GenerateOpts ->
  [HaskellTypeName] ->
  CG ()
generateParserExtractTopLevel1 GenerateOpts{isUnsafe} topTypes = do
    forM_ topTypes $ \topType -> do
        let topTypeName = bld topType.unHaskellTypeName
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
        outCodeLine' [qc|  | arr {index} ofs == 0 = (Nothing, ofs + 2)|]
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


generateModuleHeading ::
  HasCallStack =>
  GenerateOpts ->
  CG ()
generateModuleHeading GenerateOpts{..} = do
    unless isUnsafe $ outCodeLine "{-# LANGUAGE Safe #-}"
    outCodeLine "{-# LANGUAGE DuplicateRecordFields #-}"
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

