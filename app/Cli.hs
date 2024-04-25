{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
module Main(main) where
-- module Cli(main, testExpr) where

import           Control.Monad
import qualified Data.ByteString.Char8 as BS
import           Options.Applicative
import           Data.Default
import           Data.Maybe
import           Data.Version          (showVersion)
import           Development.GitRev    (gitHash)
import           Language.Haskell.RunHaskellModule
import           Paths_xml_typelift    (version)
import           Text.InterpolatedString.Perl6 (qc)
import           System.IO
import           Xeno.Errors           (printExceptions)
#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup
#endif

import           Analyze
import           CodeGen
import           Flatten
import           Parser
import           TestUtils
import Schema (Schema (..), QualNamespace, Namespace (..), qual, name, schemaLocation, impNamespace, Element (..), ElementType (..))
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.ByteString.Char8 as BSC
import Debug.Trace (trace)
import Data.Functor ((<&>))
import System.FilePath
import Control.Monad.State
import qualified Data.Set as Set


data Opts = Opts
    { schemaFilename      :: FilePath
    , isGenerateTypesOnly :: Bool
    , generateOpts        :: GenerateOpts
    , testXmlFilename     :: Maybe FilePath
    , textXmlIsPrint      :: Bool
    , outputToFile        :: Maybe FilePath
    } deriving Show

echo :: Show a => String -> a -> a
echo msg x = {- (msg <> ": " <> show x) `trace`-}  x

processSchemaRec :: FilePath -> StateT (Set.Set Namespace) IO Schema
processSchemaRec xmlFilename = do
  input <- liftIO $ BS.readFile (echo "processed xsd" xmlFilename)
  (Just schema) <- liftIO $ parseSchema input
  let currentNamespace = Namespace $ namespace schema
  modify $ Set.insert currentNamespace
  importedSchemas <- forM (imports schema) $ \import_ -> do
      qual <-
        maybe
          (error "import with no qualification")
          pure
          (List.find (\p -> impNamespace import_  == name p) (quals schema))
      pure (qual, import_)
  let qualNamespace :: QualNamespace =
        Map.fromList $ map (\w -> (qual w, Namespace $ name w)) $ quals schema
      currentTypeDict1 =
        types schema <&> \t -> [(currentNamespace, (t, qualNamespace))]
      getTopEltType elt = case eType elt of
        ElementType t -> t
        ElementRef{} -> error "elements with element refs are not supported on toplevel"
      currentElementDict1 =
        Map.fromList (map (\elt -> (eName elt, getTopEltType elt)) $ tops schema) <&> \t -> [(currentNamespace, (t, qualNamespace))]
  childTypeDicts1 <- fmap catMaybes $ forM importedSchemas $ \(_, import_) -> do
    let schemaFileName = dropFileName xmlFilename </> BSC.unpack (schemaLocation import_)
        importNamespace = Namespace import_.impNamespace
    processedSet <- get
    if Set.member importNamespace processedSet
      then pure $ echo (show importNamespace <> " is already processed") Nothing
      else Just <$> processSchemaRec schemaFileName
  pure $
    schema
    { typesExtended = Map.unionsWith (++) (currentTypeDict1 : map typesExtended childTypeDicts1)
    , elementsExtended = Map.unionsWith (++) (currentElementDict1 : map elementsExtended childTypeDicts1)
    }

processSchema :: Opts -> IO ()
processSchema Opts{..} = do
    input <- BS.readFile schemaFilename
    -- schema <- fromMaybe (error "no schema parse") <$> parseSchema input
    schema <- evalStateT (processSchemaRec schemaFilename) Set.empty
    -- print $ typesExtended schema
    -- let (flattened, msgs) = flatten schema
    -- forM_ msgs $ hPrint stderr
    let (analyzed, schemaErrors) = analyze schema -- flattened
    null schemaErrors `unless` printExceptions input schemaErrors
    let generator | isGenerateTypesOnly = codegen
                  | otherwise           = parserCodegen
    generatedFile <- generator generateOpts analyzed
    let defoutputer = maybe putStrLn (\_ _ -> return ()) testXmlFilename
    maybe defoutputer writeFile outputToFile generatedFile
    maybe (return ()) (testGeneratedParser generatedFile textXmlIsPrint) testXmlFilename


-- | Compile generated parser and run it with specified XML document
--
testGeneratedParser :: String   -- ^ Generated Parser
                    -> Bool     -- ^ Print result of parsing
                    -> FilePath -- ^ XML document for test
                    -> IO ()
testGeneratedParser generatedParser isPrintParsingResult xmlFilename =
    withTempSavedFile generatedParser "XMLSchema.hs" $ \parserFilename ->
        if isPrintParsingResult then do
            checkExitCode "Fail to print out of generated parser result" $
                runHaskellModule' (def { showStdout = True }) parserFilename ["--print", xmlFilename]
        else do
            checkExitCode "Fail to run generated parser" $
                runHaskellModule' def parserFilename [xmlFilename]
            putStrLn [qc|File {xmlFilename} processed successfully|]


main :: IO ()
main = execParser' optsParser >>= processSchema


execParser' :: ParserInfo Opts -> IO Opts
execParser' = fmap postProcessOpts . execParser
  where
    postProcessOpts opts@Opts{..}
      | isGenerateTypesOnly && isJust testXmlFilename
      = error "`--types` is not compatible with `--test-document`"
      | textXmlIsPrint && isNothing testXmlFilename
      = error "Specify test XML document for parse and print"
      | isJust testXmlFilename
      = opts { generateOpts = generateOpts { isGenerateMainFunction = True }
             , isGenerateTypesOnly = False }
      | otherwise
      = opts


optsParser :: ParserInfo Opts
optsParser =
    info (helper <*> versionOption <*> programOptions)
         (fullDesc <> progDesc "Generates types and parser for XML files by XML schema (.xsd) files" <>
             header "XML Typelift command line interface")
  where
    versionOption :: Parser (a -> a)
    versionOption = infoOption
        (concat [showVersion version, " ", $(gitHash)])
        (long "version" <> help "Show version")
    programOptions :: Parser Opts
    programOptions =
        Opts <$> filenameOption (long "schema"        <> metavar "FILENAME"  <> help "Path to XML schema (.xsd file)")
             <*> switch         (long "types"                                <> help "Generate types only")
             <*> (GenerateOpts
                 <$> switch     (long "main"                                 <> help "Generate `main` function")
                 <*> switch     (long "unsafe"                               <> help "Generate fast UNSAFE code")
                 <*> optional (strOption (long "toplevel" <> metavar "TOPLEVEL" <> help "The toplevel type required to be generated"))
                 <*> (UseXmlIsogenNaming <$> switch (long "isogen-naming" <> help "Use xml-isogen like naming conventions"))
                 <*> (ShouldGenLenses <$> switch     (long "generate-lenses"                               <> help "Generate lenses"))
                 <*> (AllowDuplicatedFields <$> switch (long "allow-duplicated-fields" <> help "Whether to allow duplicated fields"))
                 <*> switch (long "use-manual-vector-allocation" <> help "Use manual vector allocation instead of vector package (experimental)")
                 )
             <*> (optional $
                 filenameOption (long "test-document" <> metavar "FILENAME"  <> help "Path to test document (.xml file) (turn on `--main` and turn off `--types`)"))
             <*> (switch        (long "print-result"                         <> help "Print result of test document parsing"))
             <*> (optional $
                 filenameOption (long "output" <> metavar "FILENAME"         <> help "Output generated parser to FILENAME"))
    filenameOption = strOption
