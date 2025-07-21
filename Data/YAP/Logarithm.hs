{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Logarithm
-- Copyright   :  (c) Ross Paterson 2022
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: a logarithm adaptor.
--
-----------------------------------------------------------------------------

module Data.YAP.Logarithm (Logarithm, logarithm, exponential) where

import Prelude.YAP
import Data.YAP.Algebra

-- | Formal logarithm type adaptor: addition and subtraction become
-- multiplication and division on the underlying type.
newtype Logarithm a = Log a
    deriving (Eq, Ord)

instance (Show a) => Show (Logarithm a) where
    showsPrec p (Log x) =
        showParen (p > 10) $ showString "logarithm " . showsPrec 10 x

-- | Formal logarithm.
-- @'logarithm' 'zero'@ is undefined
logarithm :: (Eq a, AdditiveMonoid a) => a -> Logarithm a
logarithm x
  | x == zero = error "logarithm of zero"
  | otherwise = Log x

-- | inverse of 'logarithm'.
exponential :: Logarithm a -> a
exponential (Log x) = x

instance (Semiring a) => AdditiveMonoid (Logarithm a) where
    zero = Log one
    Log x + Log y = Log (x*y)
    atimes n (Log x) = Log (x^n)

instance (Semifield a) => AbelianGroup (Logarithm a) where
    negate (Log x) = Log (recip x)
    Log x - Log y = Log (x/y)
    gtimes n (Log x) = Log (x^^n)
