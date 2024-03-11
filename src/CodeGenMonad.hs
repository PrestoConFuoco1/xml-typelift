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

                   -- Translating identifiers
                   ,TargetIdNS(..)
                   ,XMLIdNS   (..)
                   ,getTypeFromSchema

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
                   ,FunctionBody(..)
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
import           FromXML                  (XMLString)
import           Identifiers
import           Schema
import TypeDecls1


-- | To enable tracing import Debug.Trace(trace) instead:
import qualified Debug.Trace
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import Data.String (IsString)
import Data.Bifunctor (Bifunctor(..))

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

type IdClass = (XMLIdNS, TargetIdNS)

newtype HaskellFieldName = HaskellFieldName {unHaskellFieldName :: BS.ByteString}
  deriving newtype (Eq, Ord, Show, IsString)
newtype HaskellTypeName = HaskellTypeName {unHaskellTypeName :: BS.ByteString}
  deriving newtype (Eq, Ord, Show, IsString)
mkHaskellTypeName :: XMLString -> HaskellTypeName
mkHaskellTypeName = HaskellTypeName . normalizeTypeName

newtype HaskellConsName = HaskellConsName {unHaskellConsName :: BS.ByteString}
  deriving newtype (Eq, Ord, Show, IsString)

mkHaskellConsName :: BS.ByteString -> HaskellConsName
mkHaskellConsName = HaskellConsName . normalizeTypeName

newtype FunctionBody = FunctionBody {unFunctionBody :: [String]}

-- | State of code generator
data CGState =
  CGState {
    _allocatedHaskellTypes :: Set.Set HaskellTypeName
  , _allocatedHaskellConses :: Set.Set HaskellConsName
  , _knownTypes :: Map.Map XMLString HaskellTypeName
  , _typeDecls :: [(TyData, [Record])]
  , _parseFunctions :: [FunctionBody]
  , _extractFunctions :: [FunctionBody]

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


newtype CG a = CG { unCG :: (RWS.RWS Schema CGOutput CGState a) }
  deriving (Functor, Applicative, Monad) -- , RWS.MonadReader, RWS.MonadWriter, RWS.MonadIO)

instance RWS.MonadState CGState CG where
  get       = CG   RWS.get
  put   x   = CG $ RWS.put x
  state mdf = CG $ RWS.state mdf

instance RWS.MonadWriter CGOutput CG where
  tell   = CG . RWS.tell
  listen = CG . RWS.listen . unCG
  pass   = CG . RWS.pass   . unCG

instance RWS.MonadReader Schema CG where
  reader f = CG (RWS.reader f)
  ask    = CG RWS.ask
  -- local  = CG RWS.local
  -- asks   = CG RWS.asks
  -- TODO

instance MonadFail CG where
    fail = RWS.fail

initialState :: CGState
initialState  = CGState
               (Set.fromList $ map (HaskellTypeName . snd) baseTranslations)
               (Set.fromList $ map (HaskellConsName . snd) baseTranslations)
               (Map.fromList $ map (second HaskellTypeName) baseTranslations)
               []
               []
               []
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


getTypeFromSchema :: XMLString -> CG (Maybe Type)
getTypeFromSchema name = do
  -- TODO use better lens
  Map.lookup name <$> RWS.asks types


-- | Make builder to generate schema code.
runCodeGen :: Schema -> CG () -> CGOutput
runCodeGen sch (CG rws) = case RWS.runRWS rws sch initialState of
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
