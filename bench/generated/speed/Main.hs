{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
#ifdef BENCHMARK_GENERATED_PARSER

import Criterion
import Criterion.Main
import qualified Data.ByteString as BS

import XMLSchema as X
import BenchCommon

#ifdef BENCHMARK_OTHER_TOOLS
import qualified Text.XML.Pugi as Pugi
import qualified Text.XML.Expat.Tree as Expat
import qualified Text.XML.Hexml as Hexml
import Xeno.SAX
#endif


main :: IO ()
main = defaultMain $
    flip map filenames (\(nm, filename) -> env (BS.readFile filename) (\input ->
            bgroup nm
                [ bench "parser-generated"
                    $ whnf (fromRight' . X.parse) input
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
