{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
module Tests.CodegenSpec where


import Control.Monad
import Data.Default
import Language.Haskell.RunHaskellModule
import Language.Haskell.SourceMatch
import Language.Haskell.TH.Lib
import System.FilePath.Posix
import Test.Hspec
import Text.InterpolatedString.Perl6 (qc)
import qualified GHC.Generics as G
import Control.DeepSeq

import Tests.Utils

import FromXML
import TestUtils


spec :: Spec
spec = describe "codegen" $ do
    describe "compiling" $
        forM_ ["person.xsd", "customersOrders.xsd", "shiporder.xsd", "choice.xsd", "extensions.xsd", "nested-extensions.xsd", "restriction.xsd"] $ \fn -> do
            it [qc|can compile generated types for "{fn}"|] $ example $
                tryCompile True  (inTestDir fn)
            it [qc|can compile generated parser for "{fn}"|] $ example $
                tryCompile False (inTestDir fn)
            it [qc|can parse XML generated parser for "{fn}"|] $ example $
                tryParse False (inTestDir fn) (inTestDir fn -<.> "xml")
            it [qc|can parse XML generated parser for "{fn} (unsafe)"|] $ example $
                tryParse True (inTestDir fn) (inTestDir fn -<.> "xml")
    describe "compiling types" $
        forM_ ["simple.xsd", "test.xsd", "contactExample.xsd"] $ \fn ->
            it [qc|can compile types for "{fn}"|] $ example $
                tryCompile True (inTestDir fn)
    describe "declarations presence" $ do
        it "decl.presence.1" $ example $ do
            withGeneratedFile def (inTestDir "person.xsd") $ \hsFilepath -> do
                hsFilepath `declShouldPresent`
                    [d|data Birthplace = Birthplace {
                                  city :: XMLString
                                , country :: XMLString } deriving (Show, G.Generic, NFData)|]
                hsFilepath `declShouldPresent`
                    [d|data Education = Education {
                                  degree :: XMLString
                                , yearobtained :: XMLString } deriving (Show, G.Generic, NFData)|]
                -- TODO:
                --hsFilepath `declShouldPresent`
                --    [d|data Person = Person {
                --                   name :: XMLString
                --                , age :: Integer
                --                , birthplace :: Birthplace
                --                , sex :: Integer
                --                , education :: Education }|]
        it "decl.presence.2" $ example $ do
            withGeneratedFile def (inTestDir "customersOrders.xsd") $ \hsFilepath -> do
                hsFilepath `declShouldPresent`
                    [d|data AddressType = AddressType { customerID :: Maybe XMLString,
                                                        address :: XMLString,
                                                        city :: XMLString,
                                                        region :: XMLString,
                                                        postalCode :: XMLString,
                                                        country :: XMLString} deriving (Show, G.Generic, NFData)|]


-- * --------------------------------------------------------------------------

tryCompile :: Bool -> FilePath -> IO ()
tryCompile isGenerateOnlyTypes xsdFileName =
    withGeneratedFile opts xsdFileName $ \hsFilename ->
        checkExitCode "Can't compile haskell module" $
            compileHaskellModule' compileOpts hsFilename []
  where
    opts = def { generateOnlyTypes = isGenerateOnlyTypes }

compileOpts :: RunOptions
compileOpts = def { additionalPackages = ["xml-typelift", "xeno"] }

tryParse :: Bool -> FilePath -> FilePath -> IO ()
tryParse isUnsafe xsdFileName xmlFileName =
    withGeneratedFile opts xsdFileName $ \hsFilename ->
        checkExitCode "Can't parse file with generated parser" $
            runHaskellModule' compileOpts hsFilename [xmlFileName]
  where
    opts = def { generateOnlyTypes = False, generateUnsafe = isUnsafe }

declShouldPresent :: (HasCallStack) => FilePath -> DecsQ -> Expectation
declShouldPresent hsFilepath decl =
    isFileMatchedToDecl hsFilepath decl >>= \case
        Left err -> error (show err)
        Right _  -> return ()


inTestDir :: FilePath -> FilePath
inTestDir fn = "test" </> "data" </> fn

