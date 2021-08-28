{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UnboxedTuples #-}

module Cardano.Crypto.PackedBytes (PackedBytes(..), packBytes, unpackBytes) where

import Control.DeepSeq
import Data.ByteString.Short
import Data.ByteString.Short.Internal
import Data.Primitive.ByteArray
import Data.Typeable
import Data.Word
import GHC.Exts
import GHC.ST
import GHC.TypeLits
import NoThunks.Class

data PackedBytes (n :: Nat) where
  PackedBytes28# :: Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> Word16#
                 -> PackedBytes 28
  PackedBytes32 :: {-# UNPACK #-} !Word64
                -> {-# UNPACK #-} !Word64
                -> {-# UNPACK #-} !Word64
                -> {-# UNPACK #-} !Word64
                -> PackedBytes 32
  PackedBytes# :: ByteArray# -> PackedBytes n

deriving via OnlyCheckWhnfNamed "PackedBytes" (PackedBytes n) instance NoThunks (PackedBytes n)

instance Eq (PackedBytes n) where
  x1@PackedBytes28# {} == x2 = comparePackedBytes28With eqWord16# x1 x2
  PackedBytes32 x0 x1 x2 x3 == PackedBytes32 y0 y1 y2 y3 =
    x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3
  x1 == x2 = unpackBytes x1 == unpackBytes x2

instance Ord (PackedBytes n) where
  x1@PackedBytes28# {} <= x2 = comparePackedBytes28With leWord16# x1 x2
  PackedBytes32 x0 x1 x2 x3 <= PackedBytes32 y0 y1 y2 y3 =
    x0 <= y0 && x1 <= y1 && x2 <= y2 && x3 <= y3
  x1 <= x2 = unpackBytes x1 <= unpackBytes x2

instance NFData (PackedBytes n) where
  rnf PackedBytes28# {} = ()
  rnf PackedBytes32 {}  = ()
  rnf PackedBytes# {}   = ()


unpackBytes :: PackedBytes n -> ShortByteString
unpackBytes (PackedBytes28# w00# w01# w02# w03# w04# w05# w06# w07# w08# w09# w10# w11# w12# w13#) =
  runST $ ST $ \s0# ->
    case newByteArray# 28# s0# of
      (# s1#, mba# #) ->
        let s2# = writeWord16Array# mba# 13# (extendWord16# w13#)
                  (writeWord16Array# mba# 12# (extendWord16# w12#)
                   (writeWord16Array# mba# 11# (extendWord16# w11#)
                    (writeWord16Array# mba# 10# (extendWord16# w10#)
                     (writeWord16Array# mba#  9# (extendWord16# w09#)
                      (writeWord16Array# mba#  8# (extendWord16# w08#)
                       (writeWord16Array# mba#  7# (extendWord16# w07#)
                        (writeWord16Array# mba#  6# (extendWord16# w06#)
                         (writeWord16Array# mba#  5# (extendWord16# w05#)
                          (writeWord16Array# mba#  4# (extendWord16# w04#)
                           (writeWord16Array# mba#  3# (extendWord16# w03#)
                            (writeWord16Array# mba#  2# (extendWord16# w02#)
                             (writeWord16Array# mba#  1# (extendWord16# w01#)
                              (writeWord16Array# mba#  0# (extendWord16# w00#) s1#)))))))))))))
        in case unsafeFreezeByteArray# mba# s2# of
          (# s3#, ba# #) -> (# s3#, SBS ba# #)
unpackBytes (PackedBytes32 w0 w1 w2 w3) =
  runST $ do
    mba <- newByteArray 32
    writeByteArray mba 0 w0
    writeByteArray mba 1 w1
    writeByteArray mba 2 w2
    writeByteArray mba 3 w3
    ByteArray ba# <- unsafeFreezeByteArray mba
    pure $ SBS ba#
unpackBytes (PackedBytes# ba#) = SBS ba#
{-# INLINE unpackBytes #-}



packBytes28 :: ShortByteString -> PackedBytes 28
packBytes28 (SBS ba#) =
  PackedBytes28#
    (narrowWord16# (indexWord16Array# ba# 0#))
    (narrowWord16# (indexWord16Array# ba# 1#))
    (narrowWord16# (indexWord16Array# ba# 2#))
    (narrowWord16# (indexWord16Array# ba# 3#))
    (narrowWord16# (indexWord16Array# ba# 4#))
    (narrowWord16# (indexWord16Array# ba# 5#))
    (narrowWord16# (indexWord16Array# ba# 6#))
    (narrowWord16# (indexWord16Array# ba# 7#))
    (narrowWord16# (indexWord16Array# ba# 8#))
    (narrowWord16# (indexWord16Array# ba# 9#))
    (narrowWord16# (indexWord16Array# ba# 10#))
    (narrowWord16# (indexWord16Array# ba# 11#))
    (narrowWord16# (indexWord16Array# ba# 12#))
    (narrowWord16# (indexWord16Array# ba# 13#))
{-# INLINE packBytes28 #-}


packBytes32 :: ShortByteString -> PackedBytes 32
packBytes32 (SBS ba#) =
  let ba = ByteArray ba#
  in PackedBytes32
       (indexByteArray ba 0)
       (indexByteArray ba 1)
       (indexByteArray ba 2)
       (indexByteArray ba 3)
{-# INLINE packBytes32 #-}



packBytes :: forall n . KnownNat n => ShortByteString -> PackedBytes n
packBytes sbs@(SBS ba#) =
  let px = Proxy :: Proxy n
   in case sameNat px (Proxy :: Proxy 28) of
        Just Refl -> packBytes28 sbs
        Nothing -> case sameNat px (Proxy :: Proxy 32) of
          Just Refl -> packBytes32 sbs
          Nothing   -> PackedBytes# ba#
{-# INLINE[1] packBytes #-}

packBytesN :: ShortByteString -> PackedBytes n
packBytesN (SBS ba#) = PackedBytes# ba#
{-# INLINE packBytesN #-}

{-# RULES
"packBytes28" packBytes = packBytes28
"packBytes32" packBytes = packBytes32
"packBytesN" packBytes = packBytesN
  #-}




comparePackedBytes28With :: (Word16# -> Word16# -> Int#) -> PackedBytes 28 -> PackedBytes 28 -> Bool
comparePackedBytes28With f x y =
  let !(PackedBytes28# x00# x01# x02# x03# x04# x05# x06# x07# x08# x09# x10# x11# x12# x13#) = x
      !(PackedBytes28# y00# y01# y02# y03# y04# y05# y06# y07# y08# y09# y10# y11# y12# y13#) = y
  in isTrue# (f x00# y00#) &&
     isTrue# (f x01# y01#) &&
     isTrue# (f x02# y02#) &&
     isTrue# (f x03# y03#) &&
     isTrue# (f x04# y04#) &&
     isTrue# (f x05# y05#) &&
     isTrue# (f x06# y06#) &&
     isTrue# (f x07# y07#) &&
     isTrue# (f x08# y08#) &&
     isTrue# (f x09# y09#) &&
     isTrue# (f x10# y10#) &&
     isTrue# (f x11# y11#) &&
     isTrue# (f x12# y12#) &&
     isTrue# (f x13# y13#)
{-# INLINE comparePackedBytes28With #-}

