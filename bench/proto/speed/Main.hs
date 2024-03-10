{-# LANGUAGE CPP #-}
module Main where


import Criterion
import Criterion.Main
import Xeno.SAX
import qualified Data.ByteString as BS
import BenchCommon

import Parser1
#ifdef BENCH_USE_PARSER2
import Parser2
#endif
-- import Parser3
import Parser4
import Parser5
-- import Parser6
import Parser7


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

