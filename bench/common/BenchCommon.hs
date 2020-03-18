{-# LANGUAGE CPP                 #-}
module BenchCommon where


filenames :: [(String, FilePath)]
#ifdef BENCHMARK_EXTENDED_DATA_SOURCE
filenames = [ ("32Mb",   "tmp/generated/customersOrders_00032Mb.xml")
            , ("64Mb",   "tmp/generated/customersOrders_00064Mb.xml")
                {-
            , ("128Mb",  "tmp/generated/customersOrders_00128Mb.xml")
            , ("256Mb",  "tmp/generated/customersOrders_00256Mb.xml")
            , ("512Mb",  "tmp/generated/customersOrders_00512Mb.xml")
            , ("1024Mb", "tmp/generated/customersOrders_01024Mb.xml") -- Note: about 25 sec per one file; about 7 min to whole speed benchmark
            -- , ("2048Mb", "tmp/generated/customersOrders_02048Mb.xml")
            -- , ("4096Mb", "tmp/generated/customersOrders_04096Mb.xml")
            -}
            ]
#else
filenames = [ ("16Kb",  "test/data/customersOrders.xml")
            , ("7.6Mb", "test/data/customersOrdersBig(incorrect).xml")
            ]
#endif

