{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE Strict               #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Parser where

import Prelude hiding (id)

import           Control.Monad(foldM)
import qualified Data.ByteString.Char8 as BS hiding (elem)
import           Data.ByteString.Char8(ByteString)
import           Data.List(find)
import           Data.Maybe(catMaybes, fromMaybe)
import qualified Data.Map as Map
import           System.IO(stderr)
import           Text.Read(readMaybe)
#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup((<>))
#endif

import           Xeno.DOM    as Xeno
import           Xeno.Errors as Xeno

import           Schema
import           Errors
import           FromXML
import qualified Data.List as List
import Data.String.Conversions (cs)

-- * These are internal types used only for convenient class definition.
--   Should not be exposed, but rather Schema types should be.
data TypeDesc =
  TypeDesc { tName :: !BS.ByteString
           , ty    :: !Type
           }

instance FromXML TypeDesc where
  fromXML' = goTypeDesc $ TypeDesc "" $ Complex False [] def
    where
      goTypeDesc :: TypeDesc -> Node -> Result TypeDesc
      goTypeDesc = makeFromXML (typeAttr, typeElt)
      typeAttr :: AttrHandler TypeDesc
      typeAttr tyd attr@(aName, aVal) =
        case stripNS aName of
          "name"     -> return $ tyd { tName =     aVal }
          "abstract" -> return tyd -- ignore for now
          "final"    -> return tyd -- ignore for now
          "block"    -> return tyd -- ignore for now
          "mixed"    -> return $ tyd { ty = markMixed $ ty tyd } -- TODO: ignore for now
          "type"     -> return $ tyd { ty = Ref aVal }
          "ref"      -> return $ tyd { ty = Ref aVal }
          _          -> unknownAttrHandler "type description" attr
      typeElt :: ChildHandler TypeDesc
      typeElt tyd node =
        case nodeName node of
          "annotation"  -> return tyd -- ignore annotations
          "attribute"   -> do
             attr <- fromXML' node
             return $ let TypeDesc { ty = cpl@Complex { attrs } } = tyd
                      in  tyd      { ty = cpl { attrs = attr:attrs } }
          "complexType"    -> nested -- can it be nested?
          "simpleType"     -> nested -- can it be nested?
          "complexContent" -> nested
          "simpleContent"  -> nested
          "restriction"    -> do
             restr <- handleRestriction node
             return tyd { ty = restr }
          "extension"      -> do
             TypeDesc _ newTy <- foldM typeElt tyd $ Xeno.children     node
             return tyd { ty = Extension { base  = getBaseAttribute node
                                         , mixin = newTy } }
          "all"            -> handleTyPart All
          "sequence"       -> handleTyPart Seq
          "choice"         -> handleTyPart Choice
          "attributeGroup" -> do
            attrGrp :: AttrGroupRef <- fromXML' node
            return $ let TypeDesc { ty = cpl@Complex { attrs } } = tyd
                      in  tyd      { ty = cpl { attrs = AttrGrp attrGrp:attrs } }
          "list" -> do
            let itemType = fromMaybe (error "list type without itemType reference") $ List.lookup "itemType" $ attributes node
            return $ tyd {ty = ListType itemType}
          _                -> unknownChildHandler "type description" node
        where
          -- Our parsing model does not take account of All vs Seq difference
          TypeDesc tName ty = tyd
          handleTyPart :: ([TyPart] -> TyPart) -> Result TypeDesc
          handleTyPart cons = do
            inner <- parseTyPart cons node
            return $ TypeDesc tName $ ty { inner } -- TODO: handle restricted better
          nested = goTypeDesc tyd node
  fromXML  node = case nodeName node of
                    "simpleType"  -> fromXML' node
                    "complexType" -> fromXML' node
                    "attributeGroup" -> do
                      TypeDesc { tName, ty = cpl@Complex {attrs}} <- fromXML' node
                      pure TypeDesc {tName, ty = AttrGroupType attrs}
                    otherName     -> ("Node expected to contain type descriptor is named '"
                                    <> otherName <> "'") `failHere` otherName

markMixed :: Type -> Type
markMixed cpl@(Complex {..}) = cpl { mixed=True }
markMixed x = error $ "Cannot mark type as mixed: " <> show x

instance FromXML TyPart where
  fromXML' = fromXML
  fromXML node = case nodeName node of
      "choice"  ->  parseTyPart Choice node
      "all"     ->  parseTyPart All    node
      "sequence"     ->  parseTyPart Seq    node
      "element" -> Elt <$> fromXML    node -- fromXML Element
      "any" -> pure $ Any (List.lookup "substitute" $ attributes node)
      other     -> ("Unknown type particle '" <> bshow other <> "'" <> cs (show node)) `failHere` other

-- | Parse type particle, and fix missing attribute values in case of xs:all
parseTyPart :: ([TyPart] -> TyPart) -> Xeno.Node -> Result TyPart
parseTyPart cons node =
  postprocess . cons <$>
    mapM fromXML (filter (\n -> nodeName n `notElem` unprocessed) $ Xeno.children node)
  where
  unprocessed = ["annotation", "documentation"]

-- | Fix missing minOccurs/maxOccurs in xs:all
postprocess :: TyPart -> TyPart
postprocess (All typas) = All (fixOccurs <$> typas)
  where
    fixOccurs (Elt elt@(Schema.Element {..})) = Elt $ elt { minOccurs=1, maxOccurs=MaxOccurs 1 }
    fixOccurs other                           = other
postprocess  other      = other

handleRestriction :: Xeno.Node -> Result Type
handleRestriction node = do
    restricted <- case ((`elem` ["pattern", "enumeration", "list", "union"]) . nodeName)
                          `find` Xeno.children node of
        Nothing -> return None
        Just n -> let err = (`failHere` nodeName n)
                  in case nodeName n of
                      "list"        ->  err "List restriction not yet implemented"
                      "union"       ->  err "List restriction not yet implemented"
                      "pattern"     ->  Pattern <$> getValueAttr n
                      "enumeration" -> (Enum . catMaybes) <$> mapM getEnumValue (Xeno.children node)
                      _other        ->  err "Unexpected failure in parsing <restriction>"
    return Restriction { base = getBaseAttribute node, restricted }
  where
    getEnumValue :: Xeno.Node -> Result (Maybe XMLString)
    getEnumValue eNode@(nodeName -> "enumeration") = Just <$> getValueAttr eNode
    getEnumValue _                                 = return Nothing
    getValueAttr :: Xeno.Node -> Result XMLString
    getValueAttr (findAttributeValue "value" -> Just v) = return v
    getValueAttr  aNode                                 = "Missing value attribute" `failHere` nodeName aNode

findAttributeValue :: XMLString -> Xeno.Node -> Maybe XMLString
findAttributeValue attrName node = case find ((attrName==) . fst) $ Xeno.attributes node of
  Just (_, v) -> Just v
  Nothing     -> Nothing

getBaseAttribute :: Xeno.Node -> XMLString
getBaseAttribute  = fromMaybe "" . findAttributeValue "base"

--newtype ComplexType = ComplexType Type

instance FromXML Attr where
  fromXML' = makeFromXML (attrAttr, attrElt) def
    where
      attrElt  cpl nod = case nodeName nod of
        "annotation" -> return cpl
        "simpleType" -> do
          fromXML' nod >>= \case
            TypeDesc "" ty -> return $ cpl { aType = ty }
            _              -> error "Can't match to simple type"
        _other       -> unknownChildHandler "attribute" nod
      attrAttr cpl attr@(aName, aVal) = case stripNS aName of
        "id"      -> return cpl -- ignore ids for now
        "type"    -> return $ cpl { aType = Ref aVal }
        "name"    -> return $ cpl { aName = aVal     }
        "use"     -> case aVal of
                       "prohibited" -> return cpl -- we can safely ignore, since we do not fully validate
                       "optional"   -> return cpl { use = Optional }
                       "required"   -> return cpl { use = Required } -- TODO make attributes parsing again!
                       _            -> ("Cannot parse attribute use qualifier: '" <> aVal <> "'")
                                           `failHere` aVal
        "default" -> return $ cpl { use = Default aVal }
        "fixed"   -> return $ cpl { use = Default aVal } -- TODO: treat fixed as default for now
        "form"    -> return   cpl -- ignore qualification check for now
        _other    -> unknownAttrHandler "attribute" attr

instance FromXML AttrGroupRef where
  fromXML' = makeFromXML (attrAttr, attrElt) $ AttrGroupRef ""
    where
      attrAttr cpl attr@(aName, aVal) = case stripNS aName of
        "ref" -> return cpl {ref = aVal}
        _ -> unknownAttrHandler "attributeGroup" attr
      attrElt cpl nod = case stripNS $ nodeName nod of 
        "annotation" -> return cpl
        _ -> error $ "unexpected element for attributeGroup: " <> show nod

parseSchema :: BS.ByteString -> IO (Maybe Schema)
parseSchema input = do
  --print $ skipDoctype input
  -- Note `BS.copy`: it is a quickfix for https://gitlab.com/migamake/xml-typelift/issues/11
  -- TODO remove it after fixing that issue
  case Xeno.parse $ BS.copy $ skipDoctype input of
    Left  err -> do
      BS.hPutStrLn stderr $ displayException input err
      return Nothing
    Right dom -> do
      case fromXML dom of
        Left  msg    -> do
          BS.hPutStrLn stderr $ displayException input msg
          return   Nothing
        Right schema ->
          return $ Just schema

schemaAttr :: AttrHandler Schema
schemaAttr sch attr@(aName, aVal) =
  case splitNS aName of
    (_,       "targetNamespace"     ) -> return $ sch { namespace = aVal }
    (_,       "elementFormDefault"  ) -> return sch
    (_,       "attributeFormDefault") -> return sch
    (_,       "xmlns"               ) -> return sch
    (_,       "lang"                ) -> return sch
    ("xmlns", qual                  ) -> return sch { quals = SchemaQualificator aVal (Qual qual) : quals sch}
    _                                 -> unknownAttrHandler "schema" attr

schemaElt :: ChildHandler Schema
schemaElt sch nod =
    case nodeName nod of
      "element" -> do
        elt :: Element <- fromXML' nod
        return $ sch { tops = elt:tops sch }
      "simpleType"  -> handleType
      "complexType" -> handleType
      "attributeGroup" -> handleType
      "key"         -> return sch
      "unique"      -> return sch
      "keyref"      -> return sch
      "import" -> do
        let attrs = attributes nod
        namespace <- maybe (error "import with no namespace") pure $ List.lookup "namespace" attrs
        schemaLocation <- maybe (error "import with no namespace") pure $ List.lookup "schemaLocation" attrs
        return sch { imports = SchemaImport namespace schemaLocation : imports sch}
      -- _ -> return sch -- unknownChildHandler elt val
      _ -> error $ show nod -- unknownChildHandler elt val
  where
    handleType = do
      TypeDesc label ty <- fromXML nod
      return $ addType label ty sch
      -- TODO: Find a way to add nested named elements into dictionary.


instance FromXML Element where
  fromXML  n | nodeName n == "element" = fromXML' n
  fromXML (nodeName -> nam)            = ("Expected xs:element, got '" <> nam <> "'") `failHere` nam
  fromXML' = makeFromXML (eltAttrHandler, eltChildHandler) def

eltAttrHandler :: AttrHandler Element
eltAttrHandler elt attr@(aName, aVal) =
  case splitNS aName of
    (_, "name") -> return $ elt { eName =     aVal }
    (_, "type") -> return $ elt { eType = ElementType $ Ref aVal }
    (_, "ref" ) -> return $ elt { eName = aVal, eType = ElementRef aVal}
    (_, "minOccurs") ->
      case BS.readInt aVal of
        Just  (r, "") -> return $ elt { minOccurs = r }
        _ -> ("Attribute minOccurs should be integer, but is '" <> aVal <> "'")
                             `failHere` aVal
    (_, "maxOccurs") ->
       case readMaxOccurs aVal of
         Left  err -> Left     err
         Right r   -> return $ elt { maxOccurs = r }
    (_, "default") -> return $ elt { defaultValue = Just aVal }
    ("xmlns", qual1) -> return $ elt {elQuals = Map.insert (Qual qual1) (Namespace aVal) (elQuals elt)}
    _ -> unknownAttrHandler "element" attr

readMaxOccurs :: BS.ByteString -> Result MaxOccurs
readMaxOccurs  "unbounded"                 = return Unbounded
readMaxOccurs (BS.readInt -> Just (v, "")) = return $ MaxOccurs v
readMaxOccurs  other                       = ("Cannot decode '" <> other <> "' as maxoccurs value")
                                                 `failHere` other

eltChildHandler :: ChildHandler Element
eltChildHandler elt node = case nodeName node of
    "complexType" -> handleType
    "simpleType"  -> handleType
    "annotation"  -> return     elt -- ignore
    "key"         -> return     elt
    "unique"      -> return     elt
    "keyref"      -> return     elt
    _             -> unknownChildHandler "element" node
  where
    handleType = do
      TypeDesc _ ty <- fromXML node
      return $ elt { eType = ElementType ty }

instance FromXML Schema where
  fromXML  n =
    case nodeName n of
      "schema"  -> fromXML' n
      otherName -> ("Top element should be schema, found element:" <> bshow otherName)
                       `failHere` otherName
  fromXML' = makeFromXML (schemaAttr, schemaElt) def

nodeName :: Node -> ByteString
nodeName = stripNS . Xeno.name

-- TODO use `parseError` !
readAttr :: Read a => ByteString -> a
readAttr v = case readMaybe $ BS.unpack v of
               Nothing -> parseErrorBs v "Cannot read attribute value"
               Just x  -> x

-- | Add type if name is non-empty, to the toplevel schema dictionary.
addType :: XMLString -> Type -> Schema -> Schema
addType ""     _  s                = s
addType tyName ty s@Schema {types} = s { types = Map.insert tyName ty types }

