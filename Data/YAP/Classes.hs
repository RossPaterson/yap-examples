{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Classes
-- Copyright   :  (c) Ross Paterson 2026
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- Additional classes used in the examples.
--
-----------------------------------------------------------------------------

module Data.YAP.Classes (
    -- * Differentiation and integration
    Differentiable(..), Integrable(..),
    -- * Mapping
    AdditiveFunctor(..),
  ) where

import Data.YAP.Algebra
import Prelude.YAP

-- | A differential semiring
class (Semiring a) => Differentiable a where
    -- | A monoid homomorphism that satisfies
    --
    -- * @'derivative' 'one' = 'zero'@
    --
    -- * @'derivative' (a * b) = a*'derivative' b + 'derivative' a*b@
    --
    derivative :: a -> a

-- | A differential semiring with anti-differentiation
class (Differentiable a) => Integrable a where
    -- | A monoid homomorphism that is a pre-inverse of 'derivative', i.e.
    --
    -- * @'derivative' ('integral' a) = a@
    --
    integral :: a -> a

-- | A functor on additive monoids
class AdditiveFunctor f where
    -- | Map with a function that preserves 'zero' and '(+)'.
    mapAdditive :: (AdditiveMonoid a, AdditiveMonoid b) =>
        (a -> b) -> f a -> f b
