{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.DyadicRational
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: dyadic rationals.
--
-----------------------------------------------------------------------------
module Data.YAP.DyadicRational (
    DyadicRational,
    dyadic, fromRealFloat, toRealFloat,
    ) where

import Prelude.YAP
import Data.YAP.Algebra

-- | Dyadic rationals: rational numbers whose denominator is a power of 2.
data DyadicRational = DR Integer Integer
    deriving (Eq)
-- m*2^^e, normal forms: DR 0 0 or DR m e where m is odd

instance Ord DyadicRational where
    compare (DR m1 e1) (DR m2 e2) = case compare e1 e2 of
        EQ -> compare m1 m2
        LT -> compare m1 (m2 * 2^(e2-e1))
        GT -> compare (m1 * 2^(e1-e2)) m2

-- | Show the dyadic rational in normal form: either @dyadic 0 0@ or
-- @dyadic m e@ where @m@ is odd.
instance Show DyadicRational where
    showsPrec d (DR m e) = showParen (d > app_prec) $
        showString "dyadic " . showsPrec (app_prec+1) m .
            showChar ' ' . showsPrec (app_prec+1) e
      where
        app_prec = 10

-- | A dyadic rational of the form \(m 2^e\) for any integers \(m\) and \(e\).
dyadic :: Integer -> Integer -> DyadicRational
dyadic m e
  | m == 0 = zero
  | otherwise = DR (m `div` 2^e') (e + e')
  where
    e' = exponent2 m

exponent2 :: Integer -> Integer
exponent2 n
  | n == 0 = 0
  | n < 0 = countTrailingZeros (-n)
  | otherwise = countTrailingZeros n

-- n is positive
countTrailingZeros :: Integer -> Integer
countTrailingZeros n
  | odd n = 0
  | otherwise = countTrailingZeros (n `div` 2) + 1

instance AdditiveMonoid DyadicRational where
    zero = DR 0 0
    DR m1 e1 + DR m2 e2 = case compare e1 e2 of
        EQ -> dyadic (m1 + m2) e1
        LT -> DR (m1 + m2*2^(e2-e1)) e1
        GT -> DR (m1*2^(e1-e2) + m2) e2
    atimes n (DR m e) = dyadic (toInteger n * m) e

instance AbelianGroup DyadicRational where
    negate (DR m e) = DR (-m) e
    gtimes n (DR m e) = dyadic (toInteger n * m) e

instance Semiring DyadicRational where
    one = DR 1 0
    DR m1 e1 * DR m2 e2
      | m1 == 0 || m2 == 0 = zero
      | otherwise = DR (m1*m2) (e1+e2)
    fromNatural i = dyadic (fromNatural i) 0

instance Ring DyadicRational where
    fromInteger i = dyadic i 0

-- | Units have a unit as numerator.  Standard associates have a standard
-- associate as numerator and 1 as denominator.
instance StandardAssociate DyadicRational where
    stdAssociate (DR m _) = DR (stdAssociate m) 0
    stdUnit (DR m e) = DR (stdUnit m) e
    stdRecip (DR m e) = DR (stdRecip m) (-e)

instance Euclidean DyadicRational where
    divMod (DR m1 e1) (DR m2 e2)
      | m2 == zero = error "division by zero"
      | otherwise = (dyadic q e, dyadic r e)
      where
        (q, r) = divMod m1 m2
        e = e1 - e2

    euclideanNorm (DR m _) = euclideanNorm m

instance ToRational DyadicRational where
    toRational (DR m e) = toRational m * 2^^e

-- | Exact conversion of a floating point value to a dyadic rational.
fromRealFloat :: (RealFloat a) => a -> DyadicRational
fromRealFloat x = dyadic m (toInteger e)
  where
    (m, e) = decodeFloat x

-- | Approximate conversion of a dyadic rational to a floating point value.
toRealFloat :: (RealFloat a) => DyadicRational -> a
toRealFloat (DR m e) = encodeFloat m (fromInteger e)
