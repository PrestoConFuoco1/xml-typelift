-- | Utilities for processing XML files
--
{-# LANGUAGE RecordWildCards #-}
module Tests.Utils where


import           Control.Monad
import           Data.Default
import qualified Data.ByteString.Char8 as BS


import Analyze
import CodeGen
import Flatten
import Parser
import TestUtils
import Schema (Schema (..), schemaLocation, Namespace (..), qual, name, QualNamespace)
import qualified Data.List as List
import System.FilePath
import qualified Data.ByteString.Char8 as BSC
import Debug.Trace (trace)
import qualified Data.Map as Map
import Data.Functor ((<&>))


data TestGeneratedOpts = TestGeneratedOpts
    { generateOnlyTypes :: Bool
    , generateUnsafe    :: Bool
    }

instance Default TestGeneratedOpts where
    def = TestGeneratedOpts { generateOnlyTypes = True
                            , generateUnsafe    = False
                            }

echo :: Show a => String -> a -> a
echo msg x = (msg <> ": " <> show x) `trace` x

processSchema :: FilePath -> IO Schema
processSchema xmlFilename = do
  input <- BS.readFile xmlFilename
  (Just schema) <- parseSchema input
  let currentNamespace = Namespace $ namespace schema
  importedSchemas <- forM (imports schema) $ \import_ -> do
      qual <- maybe (error "import with no qualification") pure $ List.find undefined (quals schema)
      pure (qual, import_)
  let qualNamespace :: QualNamespace =
        Map.fromList $ flip map importedSchemas $ \(q, _) -> do
          (qual q, Namespace $ name q)
      currentTypeDict1 =
        types schema <&> \t -> [(currentNamespace, (t, qualNamespace))]
  childTypeDicts1 <- forM importedSchemas $ \(_, import_) -> do
    let schemaFileName = dropFileName xmlFilename </> BSC.unpack (schemaLocation import_)
    processSchema schemaFileName
  pure $
    schema
    { typesExtended = Map.unionsWith (++) (currentTypeDict1 : map typesExtended childTypeDicts1)
    }

withGeneratedFile :: TestGeneratedOpts -> FilePath -> (FilePath -> IO ()) -> IO ()
withGeneratedFile TestGeneratedOpts{..} xmlFilename action = do
{-
    input <- BS.readFile xmlFilename
    (Just schema) <- parseSchema input
-}
{-
    importedSchemas <- forM (imports schema) $ \import_ -> do
      qual <- maybe (error "import with no qualification") pure $ List.find undefined (quals schema)
      let schemaFileName = dropFileName xmlFilename </> BSC.unpack (schemaLocation import_)
      importedInput <- BS.readFile xmlFilename
      importedSchema <- parseSchema input
      let 
      pure (qual, import_)
-}
    schema <- processSchema xmlFilename
    let (flattened, msgs) = flatten schema
    unless (null msgs) $ error ("Flattened with errors: " ++ show msgs)
    let (analyzed, schemaErrors) = analyze flattened
    unless (null schemaErrors) $ error "Schema has errors"
    result <- (if generateOnlyTypes then codegen else parserCodegen) (def { isGenerateMainFunction = True, isUnsafe = generateUnsafe }) analyzed
    withTempSavedFile result "XMLSchema.hs" action

