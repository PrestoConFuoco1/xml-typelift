{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Translating base types
--   Checking if a given type is
--   predefined Haskell type,
module BaseTypes(baseTranslations
                ,basePrologue
                ,isSimple
                ,isXSDBaseType
                ,reservedWords
                ,isBaseHaskellType
                ) where

import           Prelude               hiding (lookup)

import qualified Data.ByteString.Char8 as BS
import qualified Data.Set              as Set
#if !MIN_VERSION_base(4,11,0)
import           Data.Semigroup
#endif

import           FromXML
import           Schema
import Text.Interpolation.Nyan

-- | Module prologue to import all standard types
basePrologue :: Bool -> String
basePrologue isUnsafe = mconcat (map makeImport modules) <> "\n" <> baseTypes
  where
    makeImport modPath = "import " <> modPath <> "\n"
    modules = ["Data.Maybe"
              ,"Data.Fixed(Fixed(..))"
              ,"Data.Time.LocalTime(ZonedTime (..), TimeOfDay (..), LocalTime (..), TimeZone (..), utc, minutesToTimeZone)"
              ,"Data.Time.Format.ISO8601(iso8601ParseM)"
              ,"Data.Int(Int64)"
              ,if isUnsafe
               then "Data.Scientific (Scientific, scientific)"
               else "Data.Scientific.Safe (Scientific, scientific)"
              ,"Data.Time.ISO8601.Duration"
              -- ,"FromXML"
              -- ,"Errors"
              ,"qualified Data.Char"
              ,"qualified FlatParse.Basic as FP"
              ,"Data.Time.Calendar(Day, Year, MonthOfYear, toGregorian, fromGregorian)"
              ,"Data.Time.Calendar.Month"
              ,"Data.Time.Clock"
              -- TODO check imports:
              ,"Control.DeepSeq"
              ,"Control.Applicative"
              ,"Control.Monad.Fix"
              ,"Control.Monad.ST"
              ,"Control.Lens.TH"
              ,"qualified Data.STRef as STRef"
              ,"qualified Data.STRef.Unboxed as STRef"
              ,"Data.ByteString (ByteString)"
              ,"Data.ByteString.Internal (ByteString (..))"
              -- ,"Debug.Trace"
              -- ,"Data.Char"
              ,"Data.Functor.Identity"
              ,"Data.Time.Format"
              ,"Data.Time.LocalTime(ZonedTime)"
              ,"Data.Semigroup hiding (Product)"
              ,"Data.Word"
              ,"qualified GHC.Generics as G"
              ,"qualified Data.ByteString as BS"
              ,"qualified Data.ByteString.Char8 as BSC" -- TODO resolve with previous import
              -- TODO
              ,"Data.Either"
              -- TODO only when `isMainGenerate`
              ,"Data.List"
              ,"Prelude hiding (fail)"
              ,"System.Environment (getArgs)"
              ,"System.Exit (exitSuccess, exitFailure)"
              ,"System.IO (hPutStrLn, stderr)"
              ,"Control.Monad"
              ,"Control.Exception"
              -- ,"Data.Hashable"
              ,"System.IO.Unsafe (unsafePerformIO)"
              ,"GHC.Exts"
              ]
              ++ vectorModules
              ++ additionalBytestringModules
              ++ xenoModules
              ++ prettyPrintModules
    vectorModules
      | isUnsafe  = ["qualified Data.Vector.Unboxed as V"
                    ,"qualified Data.Vector.Unboxed.Mutable as V"]
      | otherwise = ["qualified Data.Vector.Safe as V"]
    additionalBytestringModules
      | isUnsafe  = ["qualified Data.ByteString.Unsafe as BSU"]
      | otherwise = []
    xenoModules = []
      -- | isUnsafe  = ["qualified Xeno.DOM as Xeno"]
      -- | otherwise = ["qualified Xeno.DOM.Safe as Xeno"]
    prettyPrintModules
      | isUnsafe  = [] -- "Text.Pretty.Simple"]
      | otherwise = []
    baseTypes = [int||
      {-# INLINE hash #-}
      hash :: ByteString -> Int
      hash bs = BS.foldl' f 0 bs
        where
        unI# (I# i) = i
        f (I# acc) w8 =
          I# (256# *# acc +# unI# (fromIntegral w8))

      type XMLString = ByteString
      type GYearMonth = Month
      type GYear = Year
      type GMonth = MonthOfYear
      type Unit = ()
      data SP = SP !Integer {-# UNPACK #-} !Int
      data WithTimezone a = WithTimezone { timezone :: Maybe TimeZone, value :: a }
        deriving (Show, G.Generic, NFData)
      data ArrStrOfss = ArrStrOfss !Int# !Int#
      emptyArrStrOfss :: ArrStrOfss
      emptyArrStrOfss = ArrStrOfss (-1#) (-1#)
      data ExtractResult a = ExtractResult a !Int#
      {-# INLINE getExtractResult #-}
      getExtractResult :: ExtractResult a -> a
      getExtractResult (ExtractResult x _) = x
      {-# INLINE mapExtr #-}
      mapExtr f (ExtractResult x y) = ExtractResult (f x) y
      type XDateTime = WithTimezone LocalTime
      type XTime = WithTimezone TimeOfDay
      data ErrorContext = ErrorContext
        { offset :: Int
        , input :: ByteString
        }
      data XmlTypeliftException
        = XmlParsingError Int XMLString ErrorContext
        | UnknownChoiceTag XMLString XMLString [XMLString] ErrorContext
        | RequiredAttributeMissing String String
        | UnknownEnumValue String XMLString
        | PrimitiveTypeParsingError XMLString String ErrorContext
        | InternalErrorChoiceInvalidIndex Int XMLString
        deriving anyclass Exception

      instance Show XmlTypeliftException where
        show = ppXmlTypeliftException

      ppXmlTypeliftException :: XmlTypeliftException -> String
      ppXmlTypeliftException = \\case
        XmlParsingError failOfs failTag ctx@ErrorContext{input} -> do
          let failActual = BS.take (BS.length failTag + 10) $ BS.drop failOfs input
          ppWithErrorContext ctx $
            "Expected tag '" <> BSC.unpack failTag <> "', but got '" <> BSC.unpack failActual <> "'"
        UnknownChoiceTag unexpTag hsType possibleTags ctx ->
          ppWithErrorContext ctx $
            "Unexpected tag '" <> BSC.unpack unexpTag <> "' for choice type " <> BSC.unpack hsType <> "; expected one of " <> show possibleTags
        RequiredAttributeMissing attrName hsType ->
          "Attribute '" <> attrName <> "' in type '" <> hsType <> "' is required but it's absent"
        UnknownEnumValue hsType unknownVal ->
          "Unknown enum value of type '" <> hsType <> "': " <> BSC.unpack unknownVal
        PrimitiveTypeParsingError unknownVal reason ctx ->
          ppWithErrorContext ctx $
            "Failed to parse value of primitive type; value: '" <> BSC.unpack unknownVal <> "', reason: '" <> reason <> "'"
        InternalErrorChoiceInvalidIndex consIdx hsType ->
          "Invalid code generated: wrong alternative index for choice type '" <> BSC.unpack hsType <> "': " <> show consIdx

      {-# INLINE throwWithContext #-}
      throwWithContext :: ByteString -> Int# -> (ErrorContext -> XmlTypeliftException) -> b
      throwWithContext totalInput bsOfs mkErr = throw $ mkErr $ ErrorContext (I# bsOfs) totalInput

      -- | Show error with context
      ppWithErrorContext :: ErrorContext -> String -> String
      ppWithErrorContext ErrorContext{offset=ofs, input=inputStr} msg =
        msg <> "\\nIn line " <> show lineCount <> " (offset " <> show ofs <> "):"
          <> BSC.unpack inputStrPart <> "\\n"
          <> replicate errPtrStickLen '-' <> "^"
        where
          lineCount           = succ $ BS.count nextLineChar $ BS.take ofs inputStr
          lastLineBeforeStart = maybe 0 id $ BS.elemIndexEnd nextLineChar $ til ofs
          sndLastLineStart    = maybe 0 id $ BS.elemIndexEnd nextLineChar $ til lastLineBeforeStart
          lastLineStart       = max 0 $ max (ofs - 120) sndLastLineStart
          lastLineLen         = min 40 $ maybe 40 id $ BS.elemIndex nextLineChar (BS.drop ofs inputStr)
          til len             = BS.take len inputStr
          errPtrStickLen      = max 0 (ofs - lastLineBeforeStart - 1)
          nextLineChar        = 10 -- '\\n'
          inputStrPart        = BS.take (ofs - lastLineStart + lastLineLen) $ BS.drop lastLineStart inputStr


      |]


baseTranslations :: [(BS.ByteString, BS.ByteString)]
baseTranslations =
    [("any"            , "Unit")
    ,("string"         , "XMLString"    )
    ,("boolean"        , "Bool"         )
    ,("long"           , "Int64"        ) -- or Int64
    ,("duration"       , "Duration"     ) -- TODO: ISO8601 with minor deviations
                                          -- https://www.w3.org/TR/xmlschema-2/#deviantformats
    ,("gYearMonth"     , "GYearMonth")
    ,("gYear"          , "GYear")
    ,("gMonth"         , "GMonth")
    ,("hexBinary"      , "XMLString") -- TODO: add hex decoding
    ,("base64Binary"   , "XMLString") -- TODO: add hex decoding
    ,("anyURI"         , "XMLString") -- TODO: add hex decoding
    ,("token"          , "XMLString"    )
    ,("integer"        , "Integer"      ) -- or Integer
    ,("int"            , "Int"          ) -- or Integer
    ,("positiveInteger", "Integer"      ) -- or Integer
    ,("nonNegativeInteger", "Integer")
    ,("unsignedShort", "Int")
    ,("unsignedByte", "Int")
    ,("float"          , "Float"        )
    ,("date"           , "Day"          )
    ,("time"           , "XTime"     )
    ,("dateTime"       , "XDateTime"    )
    ,("decimal"        , "Scientific"   )
    ,("double"         , "Double"       )
    ,("QName"          , "XMLString"    ) -- TODO: split namespace from QNames
    ,("NOTATION"       , "XMLString"    ) -- TODO: we ignore <xs:notation> definitions?
    ]

{-
duration - P1Y2M3DT10H30M20S - ok, P1Y2M3DT10H30M20.3S, -P1Y2M3DT10H30M20S - not ok
gYearMonth - ok
gYear - ok
gMonth - can't be parsed using standard ParseTime typeclass, added small parser
date - can use Read instance, but it doesn't handle timezones
time - 09:30:10.5 is parsed, but 09:30:10.5 is not i.e. second fractions are not supported
dateTime - parses everything except the Z timezone


-}

-- | Check if builder makes Haskell base type
isBaseHaskellType :: XMLString -> Bool
isBaseHaskellType = (`Set.member` baseHaskellTypes)

-- | List of predefined Haskell types that we use.
baseHaskellTypes :: Set.Set XMLString
baseHaskellTypes  = Set.fromList $ usedBases <> otherBases
  where
    usedBases  = map snd baseTranslations
    otherBases = ["String"
                 ,"Integer"
                 ,"Ordering"
                 ,"Maybe"
                 ,"Array"
                 ,"IORef"
                 ,"IO"
                 ,"Monad"
                 ,"()"
                 ,"Void"
                 ,"Ord"
                 ,"Eq"
                 ,"Enum"
                 ,"Bounded"
                 ,"Ordering"
                 ,"Num"
                 ,"RealFrac"
                 ,"Floating"
                 ]

-- | List of Haskell reserved words that should not clash with
--   translated identifiers.
reservedWords :: [XMLString]
reservedWords  = ["do"
                 ,"module"
                 ,"case", "of"
                 ,"if", "then", "else"
                 ,"as", "class", "instance", "where", "let"
                 ,"newtype", "data", "type"
                 ]

predefinedTypes :: Set.Set XMLString
predefinedTypes = Set.fromList $ map (("xs:" <>) . fst) baseTranslations

isXSDBaseType = (`Set.member` predefinedTypes)

isSimple :: Type -> Maybe Bool
isSimple (Ref x)
        | x    `Set.member` predefinedTypes = Just True
isSimple Restriction { base }
        | base `Set.member` predefinedTypes = Just True -- not always!!!
isSimple  Extension {}                      = Just False
isSimple  Complex   {}                      = Just False
isSimple  _                                 = Nothing -- no idea, need dictionary
