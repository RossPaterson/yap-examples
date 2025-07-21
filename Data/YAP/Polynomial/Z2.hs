{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Polynomial.Z2
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: formal polynomials
-- specialized to \({\Bbb Z}_2\), which can be represented as bit
-- sequences.
--
-----------------------------------------------------------------------------

module Data.YAP.Polynomial.Z2 (
    -- * Polynomials
    PolynomialZ2,
    fromBits,
    fromIndices,
    -- * Queries
    degree,
    bits,
    indices,
    evaluate,
    -- * Composition
    identity,
    compose,
    ) where

import Prelude.YAP
import Data.YAP.Algebra

import Data.Bits

-- | Polynomial over \({\Bbb Z}_2\), with coefficients represented by
-- the bits of
-- a value of type @a@.
newtype PolynomialZ2 a = P a
    deriving (Eq, Ord)

instance (Show a) => Show (PolynomialZ2 a) where
    showsPrec p x =
        showParen (p > 10) $
            showString "fromBits " . shows (bits x)

-- | Addition without carrying, i.e. exclusive or.
instance (Bits a) => AdditiveMonoid (PolynomialZ2 a) where
    P x + P y = P (xor x y)
    zero = P zeroBits
    atimes = timesCancelling

-- | Negation is the identity.
instance (Bits a) => AbelianGroup (PolynomialZ2 a) where
    negate (P x) = P x
    gtimes = timesCancelling

-- | Multiplication without carrying.
-- @'fromNatural' n@ is @0@ if @n@ is even and @1@ if it is odd.
instance (Bits a) => Semiring (PolynomialZ2 a) where
    x * y = sum [shiftP x i | i <- indices y]
    one = P (bit 0)

-- | @'fromInteger' n@ is @0@ if @n@ is even and @1@ if it is odd.
instance (Bits a) => Ring (PolynomialZ2 a) where

-- | The only unit is @1@. 'stdAssociate' is the identity.
instance (Bits a) => StandardAssociate (PolynomialZ2 a) where
    stdAssociate x = x
    stdUnit _ = 1
    stdRecip _ = 1

instance (Bits a) => Euclidean (PolynomialZ2 a) where
    divMod x y
      | y == 0 = error "division by zero"
      | otherwise = aux 0 x
      where
        dy = degree y
        aux q r
          | i < 0 = (q, r)
          | otherwise = aux (shiftP 1 i + q) (r - shiftP y i)
          where
            i = degree r - dy

    euclideanNorm = euclideanNorm . degree

-- | Polynomial with the given bit representation
fromBits :: a -> PolynomialZ2 a
fromBits w = P w

-- | Bit representation of a polynomial
bits :: PolynomialZ2 a -> a
bits (P w) = w

-- | Polynomial with non-zero coefficients at the listed indices
fromIndices :: (Bits a) => [Int] -> PolynomialZ2 a
fromIndices bs = sum [shiftP 1 b | b <- bs]

-- | Indices of non-zero coefficients
indices :: (Bits a) => PolynomialZ2 a -> [Int]
indices x = [i | i <- [0..degree x-1], hasIndex x i]

-- | Evaluate a polynomial for a given value of @x@.
evaluate :: (Bits a, Semiring b) => PolynomialZ2 a -> b -> b
evaluate x y =
    sum [yi | (i, yi) <- zip [0..degree x-1] (iterate (y*) one), hasIndex x i]

-- | Identity polynomial, i.e. /x/
identity :: (Bits a) => PolynomialZ2 a
identity = P (bit 1)

-- | Composition of polynomials.
compose :: (Bits a) => PolynomialZ2 a -> PolynomialZ2 a -> PolynomialZ2 a
compose = evaluate

-- | The degree of a polynomial.
degree :: (Bits a) => PolynomialZ2 a -> Int
degree (P x) = length (takeWhile (\ i -> shiftR x i /= zeroBits) [0..])

-- multiply by x^i
shiftP :: (Bits a) => PolynomialZ2 a -> Int -> PolynomialZ2 a
shiftP (P p) i = P (shiftL p i)

-- includes x^i
hasIndex :: (Bits a) => PolynomialZ2 a -> Int -> Bool
hasIndex (P xs) i = testBit xs i
