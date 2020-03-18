{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
#ifdef BENCHMARK_GENERATED_PARSER

import Criterion
import Criterion.Main
import qualified Data.ByteString as BS

import XMLSchema as X
import BenchCommon

import Parser1
#ifdef BENCH_USE_PARSER2
import Parser2
#endif
import Parser3
import Parser4
import Parser5
import Parser6
import Parser7


main :: IO ()
main = defaultMain $
    flip map filenames (\(nm, filename) -> env (BS.readFile filename) (\input ->
            bgroup nm
                [ bench "parser-generated"      $ nf X.parse input
                , bench "parser-1"              $ nf parseMethod1 input
#ifdef BENCH_USE_PARSER2
                , bench "parser-2"              $ nf parseMethod2 input
#endif
                -- , bench "parser-3-only-array"   $ nf parseToArray input
                , bench "parser-3"              $ nf parseMethod3 input
                , bench "parser-4"              $ nf parseMethod4 input
                , bench "parser-5"              $ nfAppIO parseMethod5 input
                , bench "parser-6"              $ nf parseMethod6 input
                -- , bench "parser-6-only-events"  $ nf parseMethod6OnlyEvents input
                , bench "parser-7"              $ nf parseMethod7 input
                -- , bench "parser-7-only-array"   $ nf parseToArray7 input
                ]))

#else
main :: IO ()
main = putStrLn "Benchmarking of generator parser is not enabled"
#endif
