{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# OPTIONS_GHC -funbox-strict-fields   #-}
-- | Simplification of XML Schema and RelaxNG schema
module Schema where

import           Control.DeepSeq
import           Prelude                     hiding (id)
--import Data.ByteString.Char8 as BS
--import Data.Set as Set
import           Data.Data
import           Data.Generics.Uniplate.Data ()
import           GHC.Generics

import           FromXML                     (XMLString)
import qualified Data.Map as Map

class Default a where
  def :: a

newtype Qual = Qual {unQual :: XMLString}
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)
newtype Namespace = Namespace {unNamespace :: XMLString}
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)
type QualNamespace = Map.Map Qual Namespace
type TypeDict = Map.Map XMLString Type
type TypeDict1 = Map.Map XMLString [(Namespace, (Type, QualNamespace))]

getSchemaQualNamespace :: Schema -> QualNamespace
getSchemaQualNamespace schema =
  Map.fromList $ map (\w -> (qual w, Namespace $ name w)) $ quals schema

data SchemaQualificator = SchemaQualificator
  { name :: XMLString
  , qual :: Qual
  }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

data SchemaImport = SchemaImport
  { impNamespace :: XMLString
  , schemaLocation :: XMLString
  }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

-- | Top level XML Schema
data Schema = Schema
  { quals     :: ![SchemaQualificator]
  , imports   :: ![SchemaImport]
  , types     :: !TypeDict  -- ^ Types defined by name
  , typesExtended :: !TypeDict1 -- ^ hack
  , tops      :: ![Element] -- ^ Possible top level elements
  , namespace :: !XMLString -- ^ Default namespace
  }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default Schema where
  def = Schema [] [] Map.empty Map.empty [] ""

newtype ID = ID XMLString
  deriving (Show, Read, Eq, Ord, Generic, NFData, Data, Typeable)

data MaxOccurs = Unbounded | MaxOccurs Int
  deriving (Eq, Ord, Generic, NFData, Data, Typeable, Show, Read)

type ElementName = XMLString

type NamespaceName = XMLString

data Element = Element {
    minOccurs       :: !Int
  , maxOccurs       :: !MaxOccurs
  , defaultValue :: !(Maybe XMLString)
  , eName           :: !ElementName
  , eType           :: !Type
  , targetNamespace :: !NamespaceName
  , elQuals :: !QualNamespace
  }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default Element where
  def = Element { eName           = ""
                , minOccurs       =           1
                , maxOccurs       = MaxOccurs 1
                , defaultValue = Nothing
                , eType           = def
                , targetNamespace = "" -- inherit
                , elQuals = Map.empty
                }

-- | Check that is a simple type.
simpleType :: Type -> Bool
simpleType  = undefined

validType :: Type -> Bool
validType  = undefined

data Restriction =
    Enum    ![XMLString]
  | Pattern   XMLString
  | None -- ^ No restriction expressible here
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default Restriction where
  def = None

newtype AttributeGroupType = AttributeGroupType
  { attrs :: [Attr]
  }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

data Type =
    Ref XMLString
  | Restriction {
        base       :: !XMLString
      , restricted :: !Restriction
      }
  | Extension {
        base  :: !XMLString
      , mixin :: !Type
      } -- ^ Extension of complexType
  | ListType {
      itemTypeRef :: !XMLString
      }
  | Complex {
        mixed :: !Bool
      , attrs :: ![Attr]
      , inner :: !TyPart
      }
  | AttrGroupType { attrs :: ![Attr] }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default Type where
  -- standard declares that element without type has xs:any
  def = Ref "xs:any"

data Attr = Attr {
    aName :: !XMLString
  , use   :: !Use
  , aType :: !Type
  , id    :: !(Maybe ID)
  } | AttrGrp AttrGroupRef
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default Attr where
  def = Attr { aName = ""
             , use   = Optional
             , aType = Ref "xs:string"
             , id    = Nothing
             }

data Use =
    Optional
  | Default XMLString
  | Required
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default Use where
  def = Optional

data TyPart = Seq    [TyPart]
            | Choice [TyPart]
            | All    [TyPart]
            | Group  XMLString -- named group of elements
            | Elt    Element
            | Any (Maybe XMLString)
             -- no support for xs:all yet
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

instance Default TyPart where
  def = Seq []

newtype AttrGroupRef = AttrGroupRef
  { ref :: XMLString
  }
  deriving (Eq, Ord, Show, Generic, NFData, Data, Typeable)

{-
instance NFData Attr where
  rnf (Attr a u t i) = rnf a $ rnf u $ rnf t $ rnf i
instance NFData Content
instance NFData Element
instance NFData ID
instance NFData MaxOccurs
instance NFData Restriction
instance NFData Schema
instance NFData Type
instance NFData Use
 -}
