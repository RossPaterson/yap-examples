{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Tropical
-- Copyright   :  (c) Ross Paterson 2022
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: tropical semirings.
-----------------------------------------------------------------------------

module Data.YAP.Tropical where

import Prelude.YAP
import Data.YAP.Algebra

-- | Tropical semiring
data Tropical a = Tropical a | Infinity
    deriving (Eq, Ord, Read, Show)

instance (Bounded a) => Bounded (Tropical a) where
    minBound = Tropical minBound
    maxBound = Infinity

instance (Ord a) => AdditiveMonoid (Tropical a) where
    x + y = min x y
    zero = Infinity
    atimes = atimesIdempotent

instance (Ord a, AdditiveMonoid a) => Semiring (Tropical a) where
    Tropical x * Tropical y = Tropical (x + y)
    _ * _ = Infinity
    one = Tropical zero

instance (Ord a, AbelianGroup a) => DivisionSemiring (Tropical a) where
    recip (Tropical x) = Tropical (- x)
    recip Infinity = error "reciprocal of Infinity"

instance (Ord a, AbelianGroup a) => Semifield (Tropical a)

-- | Schedule algebra or arctic semiring (dual of 'Tropical')
data Schedule a = MinusInfinity | Schedule a
    deriving (Eq, Ord, Read, Show)

instance (Bounded a) => Bounded (Schedule a) where
    minBound = MinusInfinity
    maxBound = Schedule maxBound

instance (Ord a) => AdditiveMonoid (Schedule a) where
    x + y = max x y
    zero = MinusInfinity
    atimes = atimesIdempotent

instance (Ord a, AdditiveMonoid a) => Semiring (Schedule a) where
    Schedule x * Schedule y = Schedule (x + y)
    _ * _ = MinusInfinity
    one = Schedule zero

instance (Ord a, AbelianGroup a) => DivisionSemiring (Schedule a) where
    recip (Schedule x) = Schedule (- x)
    recip MinusInfinity = error "reciprocal of MinusInfinity"

instance (Ord a, AbelianGroup a) => Semifield (Schedule a)
