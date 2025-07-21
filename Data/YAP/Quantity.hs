{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Quantity
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: numeric quantities with unit types.
-- You can only compare and add quantities that use the same units.
--
-----------------------------------------------------------------------------

module Data.YAP.Quantity (Quantity(..), scale) where

import Prelude.YAP
import Data.YAP.Algebra

-- | Quantities of a numeric type @a@, in units encoded by the phantom
-- type parameter @u@.
-- For example, types for counting apples and oranges can be defined as:
--
-- @
-- data Apple
-- data Orange
-- type Apples = Quantity Apple Int
-- type Oranges = Quantity Orange Int
-- @
--
-- You can't compare @Apples@ with @Oranges@ (or add them).
-- You can add @Apples@ to @Apples@, but not multiply them.
--
-- A full dimensional system keeping track of units while modelling
-- multiplication and division will require type-level functions.

newtype Quantity u a = Quantity a
    deriving (Eq, Ord, Read, Show)

instance (AdditiveMonoid a) => AdditiveMonoid (Quantity u a) where
    Quantity x + Quantity y = Quantity (x + y)
    zero = Quantity zero
    atimes n (Quantity x) = Quantity (atimes n x)

instance (AbelianGroup a) => AbelianGroup (Quantity u a) where
    Quantity x - Quantity y = Quantity (x - y)
    negate (Quantity x) = Quantity (negate x)
    gtimes n (Quantity x) = Quantity (gtimes n x)

-- | Multiply by a scalar
scale :: (Semiring a) => a -> Quantity u a -> Quantity u a
scale s (Quantity x) = Quantity (s*x)
