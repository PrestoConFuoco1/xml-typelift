{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
#ifdef BENCHMARK_GENERATED_PARSER

import Criterion
import Criterion.Main
import qualified Data.ByteString as BS

import XMLSchema as X

#ifdef BENCHMARK_OTHER_TOOLS
import qualified Text.XML.Pugi as Pugi
import qualified Text.XML.Expat.Tree as Expat
import qualified Text.XML.Hexml as Hexml
import Xeno.SAX
#endif


filenames :: [(String, FilePath)]
#ifdef BENCHMARK_EXTENDED_DATA_SOURCE
filenames = [ ("32Mb",  "tmp/customersOrders_00032Mb.xml")
            , ("64Mb",  "tmp/customersOrders_00064Mb.xml")
            , ("128Mb", "tmp/customersOrders_00128Mb.xml")
            , ("256Mb", "tmp/customersOrders_00256Mb.xml")
            , ("512Mb", "tmp/customersOrders_00512Mb.xml")
            , ("1024Mb",   "tmp/customersOrders_01024Mb.xml") -- Note: about 25 sec per one file; about 7 min to whole benchmark
            -- , ("2Gb",   "tmp/customersOrders_02048Mb.xml")
            -- , ("4Gb",   "tmp/customersOrders_04096Mb.xml")
            ]
#else
filenames = [ ("16Kb",  "test/customersOrders.xml")
            , ("7.6Mb", "test/customersOrdersBig(incorrect).xml")
            ]
#endif


main :: IO ()
main = defaultMain $
    flip map filenames (\(nm, filename) -> env (BS.readFile filename) (\input ->
            bgroup nm
                [ bench "parser-generated"
                    $ whnf (fromRight' . X.parser) input
                -- , bench "parser-generated-nf"
                --    $ nf X.parser input
#ifdef BENCHMARK_OTHER_TOOLS
                , bench "validate" $
                    whnf validate input
                , bench "validateEx" $
                    whnf validateEx input
                , bench "pugixml" $
                    whnf (fromRight' . Pugi.parse Pugi.def) input
                , bench "expat" $
                    whnf ((\(Right (n :: (Expat.UNode String))) -> n) . Expat.parse' Expat.defaultParseOptions) input
                , bench "hexml" $
                    whnf (fromRight' . Hexml.parse) input
#endif
                ]))


fromRight' :: Either a b -> b
fromRight' (Right r) = r
fromRight' _ = error "Wrong result"

#else
main :: IO ()
main = putStrLn "Benchmarking of generator parser is not enabled"
#endif
