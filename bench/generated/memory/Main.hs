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

#ifdef BENCHMARK_OTHER_TOOLS
import qualified Text.XML.Pugi as Pugi
import qualified Text.XML.Expat.Tree as Expat
import qualified Text.XML.Hexml as Hexml
import Xeno.SAX

instance NFData Pugi.Document where
    rnf p = p `seq` ()

instance NFData Hexml.Node where
    rnf n = n `seq` ()

#endif


main :: IO ()
main = do
    -- Due to 'weigh' use process forking we use mmaping to
    -- not read files again in forked process
    -- files' <- mapM (\(nm, fn) -> (nm,) <$> BS.readFile fn) filenames
    !files <- force <$> mapM (\(nm, fn) -> (nm,) <$> mmapFileByteString fn Nothing) filenames
    mainWith $ do
        setColumns [Case, Allocated, GCs, Max, MaxOS, MaxRss, Check]
        forM files $ \(nm, input) -> do
            func (nm ++ "_generated") X.parse input
#ifdef BENCHMARK_OTHER_TOOLS
            func (nm ++ "_validate") validate input
            func (nm ++ "_validateEx") validateEx input
            func (nm ++ "_pugixml") (fromRight' . Pugi.parse Pugi.def) input
            func (nm ++ "_expat") ((\(Right (n :: (Expat.UNode String))) -> n) . Expat.parse' Expat.defaultParseOptions) input
            func (nm ++ "_hexml") (fromRight' . Hexml.parse) input

fromRight' :: Either a b -> b
fromRight' (Right r) = r
fromRight' _ = error "Wrong result"

#endif

#else
main :: IO ()
main = putStrLn "Benchmarking of generator parser is not enabled"
#endif
