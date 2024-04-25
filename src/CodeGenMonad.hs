{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
-- | Monad for code generation:
--   Mostly deals with keeping track of all
--   generated code as "Builder",
--   keeping track of unique translation
--   for each XML identifier into Haskell
--   type or field name.
module CodeGenMonad(-- Code generation monad
                    CG
                   ,CGOutput
                   ,CGOutputEntity(..)
                   ,Env (..)
                   ,UseXmlIsogenNaming (..)
                   ,ShouldGenLenses (..)
                   ,AllowDuplicatedFields (..)
                   ,GenerateOpts (..)
                   ,runCodeGen
                   ,out
                   ,out'
                   ,outCodeLine
                   ,cut
                   ,warn
                   ,knownTypes
                   ,typeDecls
                   ,parseFunctions
                   ,extractFunctions
                   ,allocatedHaskellTypes
                   ,allocatedHaskellConses
                   ,allocatedFieldNames
                   ,processedSchemaTypes
                   ,schemaTypesMap
                   

                   -- Translating identifiers
                   ,TargetIdNS(..)
                   ,XMLIdNS   (..)

                   -- Utilities
                   ,builderUnlines
                   ,builderString
                   ,builderLength
                   ,builderIsNull
                   ,bshow
                   ,bToS

                   ,incIndent
                   ,decIndent
                   ,getIndent

                   ,HaskellFieldName(..)
                   ,HaskellTypeName
                   ,unHaskellTypeName
                   ,mkHaskellTypeName
                   ,HaskellConsName
                   ,unHaskellConsName
                   ,mkHaskellConsName
                   ,XmlNameWN (..)
                   ,FunctionBody(..)
                   ,TypeWithAttrs(..)
                   ,AttributesInfo(..)
                   ,typeNoAttrs
                   ,GIType (..)
                   ,SequenceGI(..)
                   ,ChoiceGI(..)
                   ,EnumGI(..)
                   ,NewtypeGI(..)
                   ,ListGI(..)
                   ,Repeatedness (..)
                   ,FieldGI (..)
                   ,ContentWithAttrsGI (..)
                   ,knownBaseTypes
                   ,mkXmlNameWN
                   ,AttrFieldGI (..)
                   ,InTagInfo(..)
                   ) where

import           Prelude                  hiding (lookup)

import           Control.Lens             as Lens
import           Control.Monad.Fail
-- import           Text.InterpolatedString.Perl6 (qc)
import qualified Control.Monad.RWS.Strict as RWS
import qualified Data.ByteString.Builder  as B
import qualified Data.ByteString.Char8    as BS
import qualified Data.ByteString.Lazy     as BSL (length, null, toStrict)
import qualified Data.Map.Strict          as Map
import qualified Data.Set                 as Set
import qualified Language.Haskell.TH      as TH
#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup((<>))
#endif

import           BaseTypes
import           FromXML                  (XMLString, splitNS)
import           Identifiers
import           Schema
import TypeDecls1


-- | To enable tracing import Debug.Trace(trace) instead:
import qualified Debug.Trace
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import Data.String (IsString)
import Data.Bifunctor (Bifunctor(..))
import qualified Data.List.NonEmpty as NE
import Text.InterpolatedString.Perl6
import GHC.Generics (Generic)

trace :: HasCallStack => String -> a -> a
trace msg = Debug.Trace.trace (msg <> "\n  " <> prettyCallStack callStack)

-- | Which of the XML Schema identifier namespaces do we use here
data XMLIdNS = SchemaType
             | ElementName
             | AttributeName
             | EnumIn XMLString -- enumeration inside type/element of given name (should be path)
             | ChoiceIn XMLString -- xs:choice inside type of given name
             | SchemaGroup
  deriving (Eq, Ord, Show)

-- | Which of the target language identifier namespaces do we use here
data TargetIdNS = TargetTypeName
                | TargetConsName
                | TargetFieldName
  deriving (Eq, Ord, Show, Enum, Bounded)

newtype HaskellFieldName = HaskellFieldName {unHaskellFieldName :: BS.ByteString}
  deriving newtype (Eq, Ord, Show, IsString, ShowQ)
newtype HaskellTypeName = HaskellTypeName {unHaskellTypeName :: BS.ByteString}
  deriving newtype (Eq, Ord, Show, IsString, ShowQ)
mkHaskellTypeName :: XMLString -> HaskellTypeName
mkHaskellTypeName = HaskellTypeName . normalizeTypeName

newtype HaskellConsName = HaskellConsName {unHaskellConsName :: BS.ByteString}
  deriving newtype (Eq, Ord, Show, IsString, ShowQ)

mkHaskellConsName :: XMLString -> HaskellConsName
mkHaskellConsName = HaskellConsName . normalizeTypeName

newtype FunctionBody = FunctionBody {unFunctionBody :: [String]}

newtype XmlNameWN = XmlNameWN {unXmlNameWN :: XMLString}
  deriving newtype (Eq, Ord, Show, IsString, ShowQ, Semigroup)

mkXmlNameWN :: XMLString -> XmlNameWN
mkXmlNameWN = XmlNameWN . snd . splitNS

data TypeWithAttrs = TypeWithAttrs
  { type_ :: HaskellTypeName
  , giType :: GIType
  }
  deriving stock (Show)

data AttributesInfo
  = NoAttrs
  | AttributesInfo
    { attrs :: NE.NonEmpty XMLString
    }
  deriving stock (Eq, Show)

typeNoAttrs :: HaskellTypeName -> GIType -> TypeWithAttrs
typeNoAttrs = TypeWithAttrs

data InTagInfo = InTagInfo
  { tagName :: XMLString
  , occurs :: Repeatedness
  , defaultVal :: Maybe XMLString
  -- ^ only for simple contents
  }
  deriving stock (Show)

data GIType
  = GBaseType
  | GAttrContent ContentWithAttrsGI
  | GSeq SequenceGI
  | GChoice ChoiceGI
  | GEnum EnumGI
  | GWrapper NewtypeGI
  | GList ListGI
  deriving stock (Show)

data ContentWithAttrsGI = ContentWithAttrsGI
  { typeName :: HaskellTypeName
  , consName :: HaskellConsName
  , attributes :: [AttrFieldGI]
--  , contentFieldName :: HaskellFieldName
--  , contentType :: HaskellTypeName
  , content :: FieldGI
  }
  deriving stock (Show, Generic)

-- GI stands for "generating input"
-- type for processing sequence inside complexType
data SequenceGI = SequenceGI
  { typeName :: HaskellTypeName
  , consName :: HaskellConsName
  , attributes :: [AttrFieldGI]
  , fields :: [FieldGI]
  }
  deriving stock (Show, Generic)

data ChoiceGI = ChoiceGI
  { typeName :: HaskellTypeName
  , alts :: [(Maybe InTagInfo, [XMLString], HaskellConsName, TypeWithAttrs)]
  }
  deriving stock (Show)

data AttrFieldGI = AttrFieldGI
  { haskellName :: HaskellFieldName
  , xmlName :: XMLString
  , typeName :: TypeWithAttrs
  , attrUse :: Use
  }
  deriving stock (Show)

data FieldGI = FieldGI
  { haskellName :: HaskellFieldName
  , typeName :: TypeWithAttrs
  , inTagInfo :: Maybe InTagInfo
  }
  deriving stock (Show)

data EnumGI = EnumGI
  { typeName :: HaskellTypeName
  , constrs :: [(XMLString, HaskellConsName)]
  }
  deriving stock (Show)

data NewtypeGI = NewtypeGI
  { typeName :: HaskellTypeName
  , consName :: HaskellConsName
  , wrappedType :: TypeWithAttrs
  }
  deriving stock (Show)
 
data ListGI = ListGI
  { typeName :: HaskellTypeName
  , consName :: HaskellConsName
  , itemType :: HaskellTypeName
  }
  deriving stock (Show)

data Repeatedness = RepMaybe
                  | RepOnce
                  | RepMany
                  | RepNotLess Int
                  | RepRange Int Int
                  deriving Show

-- | State of code generator
data CGState =
  CGState {
    _allocatedHaskellTypes :: Set.Set HaskellTypeName
  , _allocatedHaskellConses :: Set.Set HaskellConsName
  , _allocatedFieldNames :: Set.Set HaskellFieldName
  , _knownTypes :: Map.Map XmlNameWN [(Namespace, TypeWithAttrs)]
  , _typeDecls :: [TypeDecl]
  , _parseFunctions :: [FunctionBody]
  , _extractFunctions :: [FunctionBody]
  , _processedSchemaTypes :: Set.Set XMLString
  -- , _schemaTypesMap :: Map.Map XMLString Type
  , _schemaTypesMap :: Map.Map XmlNameWN [(Namespace, (Type, QualNamespace))]
  , _knownSchemaElements :: Map.Map XmlNameWN [(Namespace, (Type, QualNamespace))]
  , _knownElements :: Map.Map XmlNameWN [(Namespace, TypeWithAttrs)]

  -- FOR GENERATING
  , _indent               :: Int
  }
makeLenses ''CGState


data CGOutputEntity = CGDec (TH.Q TH.Dec)
                    | CGCodeLine String
                    | CGDecs TH.DecsQ


type CGOutput = [CGOutputEntity]


-- | `(a, w) <- cut wrt` redirects all output from wrt to `w`.
--
cut :: RWS.MonadWriter w m => m a -> m (a, w)
cut act = RWS.pass $ do
    r <- RWS.listen act
    return (r, const mempty)

newtype CG a = CG { unCG :: RWS.RWS Env CGOutput CGState a }
  deriving (Functor, Applicative, Monad) -- , RWS.MonadReader, RWS.MonadWriter, RWS.MonadIO)

instance RWS.MonadState CGState CG where
  get       = CG   RWS.get
  put   x   = CG $ RWS.put x
  state mdf = CG $ RWS.state mdf

instance RWS.MonadWriter CGOutput CG where
  tell   = CG . RWS.tell
  listen = CG . RWS.listen . unCG
  pass   = CG . RWS.pass   . unCG

newtype UseXmlIsogenNaming = UseXmlIsogenNaming Bool
  deriving Show

newtype ShouldGenLenses = ShouldGenLenses Bool
  deriving Show

newtype AllowDuplicatedFields = AllowDuplicatedFields Bool
  deriving Show

-- | Options for generating
data GenerateOpts = GenerateOpts
    { isGenerateMainFunction :: Bool
    , isUnsafe               :: Bool
    , topName :: Maybe String
    , useXmlIsogenNaming :: UseXmlIsogenNaming
    , shouldGenerateLenses :: ShouldGenLenses
    , allowDuplicatedFields :: AllowDuplicatedFields
    } deriving Show

instance Default GenerateOpts where
    def = GenerateOpts False False Nothing (UseXmlIsogenNaming False) (ShouldGenLenses False) (AllowDuplicatedFields False)

data Env = Env
  { genOpts :: GenerateOpts
  , schema :: Schema
  }

instance RWS.MonadReader Env CG where
  reader f = CG (RWS.reader f)
  ask    = CG RWS.ask
  -- local  = CG RWS.local
  -- asks   = CG RWS.asks
  -- TODO

instance MonadFail CG where
    fail = RWS.fail

defaultNamespace :: Namespace
defaultNamespace = Namespace "http://www.w3.org/2001/XMLSchema"


knownBaseTypes :: Map.Map XmlNameWN TypeWithAttrs
knownBaseTypes = Map.fromList $ map (bimap mkXmlNameWN (flip typeNoAttrs GBaseType . HaskellTypeName)) baseTranslations

initialState :: CGState
initialState  = CGState
               (Set.fromList $ map (HaskellTypeName . snd) baseTranslations)
               (Set.fromList $ map (HaskellConsName . snd) baseTranslations)
               Set.empty
               (Map.fromList $ map (bimap mkXmlNameWN ((:[]) . (defaultNamespace,) .  flip typeNoAttrs GBaseType . HaskellTypeName)) baseTranslations)
               []
               []
               []
               Set.empty
               Map.empty
               Map.empty
               Map.empty
               0

out :: TH.Q TH.Dec -> CG ()
out dec = RWS.tell [CGDec dec]

out' :: TH.DecsQ -> CG ()
out' decs = RWS.tell [CGDecs decs]

outCodeLine :: String -> CG ()
outCodeLine cmnt = RWS.tell [CGCodeLine cmnt]

warn :: String -> CG ()
warn wrn = outCodeLine $ concat ["{- WARNING ", wrn, " -}"]

-- TODO: add keywords to prevent mapping of these

bshow :: Show a => a -> BS.ByteString
bshow = BS.pack . show

builderUnlines :: [B.Builder] -> B.Builder
builderUnlines []     = ""
builderUnlines (l:ls) = l <> mconcat (("\n" <>) <$> ls)

-- | Make builder to generate schema code.
runCodeGen :: GenerateOpts -> Schema -> CG () -> CGOutput
runCodeGen opts sch (CG rws) = case RWS.runRWS rws (Env opts sch) initialState of
                            ((), _state, output) -> output

-- | Convert builder back to String, if you need to examine the content.
builderString :: B.Builder -> BS.ByteString
builderString  = BSL.toStrict . B.toLazyByteString

builderLength :: B.Builder -> Int
builderLength  = fromIntegral . BSL.length . B.toLazyByteString

builderIsNull :: B.Builder -> Bool
builderIsNull = BSL.null . B.toLazyByteString

bToS :: B.Builder -> String
bToS = BS.unpack . BSL.toStrict . B.toLazyByteString



incIndent :: CG ()
incIndent = do
    st@CGState{_indent} <- RWS.get
    RWS.put $ st { _indent = _indent + 2 }


decIndent :: CG ()
decIndent = do
    st@CGState{_indent} <- RWS.get
    RWS.put $ st { _indent = _indent - 2 }


getIndent :: CG Int
getIndent = RWS.gets _indent
