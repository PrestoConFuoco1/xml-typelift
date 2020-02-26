{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
#ifdef BENCHMARK_GENERATED_PARSER


import Control.DeepSeq
import Control.Monad
import System.IO.MMap
import Weigh

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
main = do
    -- Due to 'weigh' use process forking we use mmaping to
    -- not read files again in forked process
    -- files' <- mapM (\(nm, fn) -> (nm,) <$> BS.readFile fn) filenames
    !files <- force <$> mapM (\(nm, fn) -> (nm,) <$> mmapFileByteString fn Nothing) filenames
    mainWith $
        forM files $ \(nm, input) -> do
            func (nm ++ "_generated") X.parse input
            func (nm ++ "_parser1") parseMethod1 input
#ifdef BENCH_USE_PARSER2
            func (nm ++ "_parser2") parseMethod2 input
#endif
            func (nm ++ "_parser3") parseMethod3 input
            func (nm ++ "_parser4") parseMethod4 input
            io   (nm ++ "_parser5") parseMethod5 input
            func (nm ++ "_parser6") parseMethod6 input
            func (nm ++ "_parser7") parseMethod7 input


#else
main :: IO ()
main = putStrLn "Benchmarking of generator parser is not enabled"
#endif
