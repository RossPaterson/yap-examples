{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.UnitInterval
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- Semirings on the unit interval.
--
-----------------------------------------------------------------------------

module Data.YAP.UnitInterval (
    -- * Bounded intervals
    MaxMin(..),
    -- * Unit intervals
    UnitInterval, toUnitInterval, fromUnitInterval,
    Viterbi(..),
    Lukasiewicz(..),
    ) where

import Prelude.YAP
import Data.YAP.Algebra

-- | Max-min semiring.
-- The special case @'MaxMin' 'Bool'@ is the two-element Boolean semiring.
newtype MaxMin a = MaxMin a
    deriving (Bounded, Eq, Ord, Read, Show)

-- | addition is maximum
instance (Bounded a, Ord a) => AdditiveMonoid (MaxMin a) where
    (+) = max
    zero = minBound
    atimes = atimesIdempotent

-- | multiplication is minimum
instance (Bounded a, Ord a, AdditiveMonoid a) => Semiring (MaxMin a) where
    (*) = min
    one = maxBound

-- | The interval [0, 1] in an ordered semiring.
newtype UnitInterval a = UnitInterval a
    deriving (Eq, Ord)

instance (Ord a, Semiring a) => Bounded (UnitInterval a) where
    minBound = UnitInterval zero
    maxBound = UnitInterval one

instance (Show a) => Show (UnitInterval a) where
    showsPrec p (UnitInterval x) =
        showParen (p > 10) $ showString "toUnitInterval " . showsPrec 10 x

-- | The nearest value within the unit interval.
toUnitInterval :: (Ord a, Semiring a) => a -> UnitInterval a
toUnitInterval x = UnitInterval (max zero (min one x))

-- | Embedding of the unit interval in the original ring.
--
-- prop> toUnitInterval . fromUnitInterval = id
--
fromUnitInterval :: UnitInterval a -> a
fromUnitInterval (UnitInterval x) = x

multiply :: (Semiring a) => UnitInterval a -> UnitInterval a -> UnitInterval a
multiply (UnitInterval x) (UnitInterval y) = UnitInterval (x*y)

-- | The Viterbi or product semiring
newtype Viterbi a = Viterbi (UnitInterval a)
    deriving (Eq, Ord, Show)

-- | addition is maximum
instance (Ord a, AdditiveMonoid a) => AdditiveMonoid (Viterbi a) where
    Viterbi x + Viterbi y = Viterbi (max x y)
    zero = Viterbi (UnitInterval zero)
    atimes = atimesIdempotent

-- | uses multiplication of the underlying semiring
instance (Ord a, Semiring a) => Semiring (Viterbi a) where
    Viterbi x * Viterbi y = Viterbi (multiply x y)
    one = Viterbi (UnitInterval one)

-- | The Łukasiewicz semiring
newtype Lukasiewicz a = Lukasiewicz (UnitInterval a)
    deriving (Eq, Ord, Show)

-- | addition is maximum
instance (Ord a, AdditiveMonoid a) => AdditiveMonoid (Lukasiewicz a) where
    Lukasiewicz x + Lukasiewicz y = Lukasiewicz (max x y)
    zero = Lukasiewicz (UnitInterval zero)
    atimes = atimesIdempotent

instance (Ord a, Ring a) => Semiring (Lukasiewicz a) where
    Lukasiewicz x * Lukasiewicz y =
        Lukasiewicz $ UnitInterval $
            max zero (fromUnitInterval x + fromUnitInterval y - 1)
    one = Lukasiewicz (UnitInterval one)
