-- | Generating type declarations in code generation monad.
{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
module TypeDecls1 where


import           Control.Monad
import qualified Data.ByteString.Builder    as B
import           Language.Haskell.TH.Syntax as TH hiding (SumAlt)


-- TODO: type alias these for safety
-- * Type declarations
newtype TyData      = TyData B.Builder
newtype TyCon       = TyCon B.Builder
newtype TyType      = TyType B.Builder
newtype TyFieldName = TyFieldName B.Builder

type TyField  = (TyFieldName, -- field name
                 TyType)    -- field type
type Record = (TyCon,     -- Constructor name
               [TyField])

-- | Sum type without single record field for each constructor.
type SumType = (TyData -- ^ Type name
               ,[SumAlt]
               )


type SumAlt = (TyCon -- ^ Constructor name
              ,TyType -- ^ Type under the constructor
              )

data TypeDecl
  = Alg (TyData, [Record])
  | Newtype (TyData, TyCon, TyType)


