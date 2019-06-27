{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Abstract hashing functionality.
module Cardano.Crypto.Hash.Class
  ( HashAlgorithm (..)
  , ByteString
  , Hash
  , getHash
  , hash
  , hashWithSerialiser
  , fromHash
  )
where

import Cardano.Binary
  ( Encoding
  , FromCBOR (..)
  , ToCBOR (..)
  , decodeBytes
  , serializeEncoding'
  )
import Data.ByteString (ByteString)
import qualified Data.ByteString as SB
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as SB8
import Data.List (foldl')
import Data.Proxy (Proxy (..))
import Data.String (IsString (..))
import Data.Typeable (Typeable)
import Data.Word (Word8)
import GHC.Generics (Generic)
import GHC.Stack
import Numeric.Natural

class Typeable h => HashAlgorithm h where

  byteCount :: proxy h -> Natural

  digest :: HasCallStack => proxy h -> ByteString -> ByteString

newtype Hash h a = Hash {getHash :: ByteString}
  deriving (Eq, Ord, Generic)

instance Show (Hash h a) where
  show = SB8.unpack . B16.encode . getHash

instance IsString (Hash h a) where
  fromString = Hash . fst . B16.decode . SB8.pack

instance (HashAlgorithm h, Typeable a) => ToCBOR (Hash h a) where
  toCBOR = toCBOR . getHash

instance (HashAlgorithm h, Typeable a) => FromCBOR (Hash h a) where
  fromCBOR = do
    bs <- decodeBytes
    let la = SB.length bs
        le :: Int
        le = fromIntegral $ byteCount (Proxy :: Proxy h)
    if la == le
    then return $ Hash bs
    else fail $ "expected " ++ show le ++ " byte(s), but got " ++ show la

hash :: forall h a. (HashAlgorithm h, ToCBOR a) => a -> Hash h a
hash = hashWithSerialiser toCBOR

hashWithSerialiser :: forall h a. HashAlgorithm h => (a -> Encoding) -> a -> Hash h a
hashWithSerialiser toEnc = Hash . digest (Proxy :: Proxy h) . serializeEncoding' . toEnc

fromHash :: Hash h a -> Natural
fromHash = foldl' f 0 . SB.unpack . getHash
  where
    f :: Natural -> Word8 -> Natural
    f n b = n * 256 + fromIntegral b
