{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ViewPatterns        #-}
-- | Here we aim to analyze the schema.
module CodeGen(codegen) where

import           Prelude hiding(lookup)

import           Control.Lens as Lens
import           Control.Monad(forM, forM_)
--import qualified Control.Monad.State.Class  as St
--import qualified Control.Monad.Writer.Class as Writer
--import qualified Control.Monad.Reader.Class as Reader
import qualified Control.Monad.RWS.Strict   as RWS
import qualified Data.ByteString.Char8      as BS
import qualified Data.ByteString.Lazy       as BSL(length, toStrict)
import qualified Data.ByteString.Builder    as B
import           Data.Generics.Uniplate.Operations
import qualified Data.Map.Strict            as Map
import           Data.Maybe(catMaybes)
import qualified Data.Set                   as Set
import           Data.String

import           Xeno.Types(XenoException(..))

import           FromXML(getStartIndex, stripNS)
import           Identifiers
import           Schema
import           CodeGenMonad


-- | Returns a pair of field name, and type code.
generateElementInstance :: XMLString -- container name
                        -> Element -> CG (B.Builder, B.Builder)
generateElementInstance container elt@(Element {minOccurs, maxOccurs, eName, ..}) =
    (,) <$>  translateField                  container eName
        <*> (wrapper <$> generateElementType container elt  )
  where
    wrapper tyName | minOccurs==1 && maxOccurs==MaxOccurs 1 =             tyName
                   | minOccurs==0 && maxOccurs==MaxOccurs 1 = "Maybe " <> tyName
                   | otherwise                              = "["      <> tyName <> "]"
generateElementInstance container _ = return ( B.byteString container
                                             , "generateElementInstanceNotFullyImplemented" )

generateElementType :: XMLString -- container name
                    -> Element
                    -> CG B.Builder
-- Flatten elements with known type to their types.
generateElementType container (eType -> Ref (stripNS -> ""    )) = return "ElementWithEmptyRefType"
generateElementType container (eType -> Ref (stripNS -> tyName)) = translateType container tyName
generateElementType container (Element {eName, eType = Complex attrs content})   = do
    myTypeName  <- translateType container eName
    attrFields  :: [Field] <- mapM makeAttrType attrs
    childFields :: [Field] <- case content of -- serving only simple Seq of elts or choice of elts for now
      Seq    ls -> seqInstance ls
      Choice ls -> (:[]) <$> makeAltType ls
    RWS.tell $ "data " <> myTypeName <> " ="
    declareAlgebraicType [(myTypeName, attrFields <> childFields)]
    return      myTypeName
  where
    makeAttrType :: Attr -> CG (B.Builder, B.Builder)
    makeAttrType Attr {..} = mapSnd (wrapper use) <$> makeFieldType aName aType
    mapSnd f (a, b) = (a, f b)
    wrapper :: Schema.Use -> B.Builder -> B.Builder
    wrapper  Optional   ty = "Maybe " <> ty
    wrapper  Required   ty =             ty
    wrapper (Default x) ty =             ty
    makeFieldType :: XMLString -> Type -> CG (B.Builder, B.Builder)
    makeFieldType  aName aType = (,) <$> translateField      eName aName
                                     <*> generateContentType eName aType
    makeAltType :: [TyPart] -> CG (B.Builder, B.Builder)
    makeAltType ls = return ("altFields", "AltTypeNotYetImplemented")
    seqInstance = mapM fun
      where
        fun (Elt (elem@(Element {eName=subName}))) = do
          (name, ty) <- generateElementInstance eName elem
          generateElementInstance eName elem

generateContentType :: XMLString -- container name
                    -> Type -> CG B.Builder
generateContentType container (Ref tyName) = translateType container tyName
  -- TODO: check if the type was already translated (as it should, if it was generated)
generateContentType _          other       = return "NotYetImplemented"

-- | Make builder to generate schema code
codegen    :: Schema -> B.Builder
codegen sch = runCodeGen sch $ generateSchema sch

generateSchema sch = do
    RWS.tell "module XMLSchema where\n"
    RWS.tell "import FromXML\n"
    -- First generate all types that may be referred by others.
    _               <- generateContentType "Top" `mapM` types sch
    -- Then generate possible top level types.
    topElementTypeNames <- generateElementType "Top" `mapM` tops sch
    case topElementTypeNames of
      []                   -> fail "No toplevel elements found!"
      [eltName] | baseHaskellType (builderString eltName) ->
           RWS.tell $ "newtype TopLevel = TopLevel "    <> eltName
      [eltName]                                           ->
           RWS.tell $ "type " <> topLevelConst <> " = " <> eltName
      (firstAlt:otherAlts) -> RWS.tell $ "data TopLevel =\n"                 <>
                                            genFirstAlt             firstAlt <>
                                            mconcat (genNextAlt <$> otherAlts)
    RWS.tell "\n"
  where
    genFirstAlt, genNextAlt, genAlt :: B.Builder -> B.Builder
    genFirstAlt alt = "    " <> genAlt alt
    genNextAlt  alt = "  | " <> genAlt alt
    genAlt typeName = "Top" <> typeName <> " " <> typeName
    topLevelConst = "TopLevel"

