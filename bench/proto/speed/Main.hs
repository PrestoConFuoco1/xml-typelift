{-# LANGUAGE CPP #-}
module Main where


import Criterion
import Criterion.Main
import Xeno.SAX
import qualified Data.ByteString as BS

import Parser1
#ifdef BENCH_USE_PARSER2
import Parser2
#endif
import Parser3
import Parser4
import Parser5
import Parser6
import Parser7


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
filenames = [ ("16Kb",  "test/data/customersOrders.xml")
            , ("7.6Mb", "test/data/customersOrdersBig(incorrect).xml")
            ]
#endif


main :: IO ()
main =
    defaultMain $
        map (\(nm, filename) -> env (BS.readFile filename) (\input ->
                bgroup nm
                    [ bench "validate"              $ nf validate     input
                    , bench "validateEx"            $ nf validateEx   input
                    , bench "parser-1"              $ nf parseMethod1 input
#ifdef BENCH_USE_PARSER2
                    , bench "parser-2"              $ nf parseMethod2 input
#endif
                    , bench "parser-3-only-array"   $ nf parseToArray input
                    , bench "parser-3"              $ nf parseMethod3 input
                    , bench "parser-4"              $ nf parseMethod4 input
                    , bench "parser-5"              $ nfAppIO parseMethod5 input
                    , bench "parser-6"              $ nf parseMethod6 input
                    , bench "parser-6-only-events"  $ nf parseMethod6OnlyEvents input
                    , bench "parser-7"              $ nf parseMethod7 input
                    , bench "parser-7-only-array"   $ nf parseToArray7 input
                    ]))
            filenames
