{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds, KindSignatures #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Vector
-- Copyright   :  (c) Ross Paterson 2023
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  type-level literals
--
-- An example instance of the algebraic classes: vectors.
--
-----------------------------------------------------------------------------

module Data.YAP.Vector (
    Vector, vector, unsafeVector, coordinates, dot, sqnorm,
    ) where

import Prelude.YAP
import Data.YAP.Algebra

import GHC.TypeLits

-- | Vectors on @n@ elements
newtype Vector (n::Nat) a = Vector [a]
    deriving (Eq, Ord)

instance (Show a) => Show (Vector n a) where
    showsPrec p (Vector xs) =
        showParen (p > 10) $ showString "vector " . shows xs

instance Functor (Vector n) where
    fmap f (Vector xs) = Vector (fmap f xs)

instance (KnownNat n) => Applicative (Vector n) where
    pure x = makeVector (repeat x)
    Vector fs <*> Vector xs = Vector (zipWith ($) fs xs)

-- | Construct a vector from a list of coordinates, trimming or padding
-- with zeros to obtain the required length.
vector :: (KnownNat n, AdditiveMonoid a) => [a] -> Vector n a
vector xs = makeVector (xs ++ repeat zero)

-- | Construct a vector from a list of coordinates: valid only if the
-- list has length @n@.
unsafeVector :: [a] -> Vector n a
unsafeVector xs = Vector xs

-- Construct a vector from an infinite list.
makeVector :: (KnownNat n) => [a] -> Vector n a
makeVector xs = makeVectorSing $ \ n ->
    Vector (take (fromInteger (natVal n)) xs)

-- helper to provide a singleton for n
makeVectorSing :: (KnownNat n) => (SNat n -> Vector n a) -> Vector n a
makeVectorSing k = k natSing

-- | The coordinates of a vector
coordinates :: Vector n a -> [a]
coordinates (Vector xs) = xs

zipVectorWith :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipVectorWith f (Vector xs) (Vector ys) = Vector (zipWith f xs ys)

instance Foldable (Vector n) where
    foldMap f (Vector xs) = foldMap f xs
    foldr z f (Vector xs) = foldr z f xs

instance (KnownNat n, AdditiveMonoid a) => AdditiveMonoid (Vector n a) where
    (+) = zipVectorWith (+)
    zero = pure zero
    atimes n = fmap (atimes n)

instance (KnownNat n, AbelianGroup a) => AbelianGroup (Vector n a) where
    (-) = zipVectorWith (-)
    negate = fmap negate
    gtimes n = fmap (gtimes n)

-- | Dot product of two vectors.
dot :: (Semiring a) => Vector n a -> Vector n a -> a
dot u v = sum (zipVectorWith (*) u v)

-- | Squared norm of a vector.
sqnorm :: (Semiring a) => Vector n a -> a
sqnorm v = v `dot` v
