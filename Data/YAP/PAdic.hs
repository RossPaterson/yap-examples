{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE KindSignatures #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Polynomial
-- Copyright   :  (c) Ross Paterson 2025
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: /p/-adic numbers,
-- an extension of the rationals for each prime /p/.
--
-----------------------------------------------------------------------------

module Data.YAP.PAdic(
    -- * /p/-adic numbers
    PAdic,
    PAdicInteger,
    fromPAdicInteger,
    digits,
    pAdicInteger,
    fromPAdic,
    maybeSqrt,
    ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Ratio
import Data.YAP.PowerSeries

import Data.Maybe
import GHC.TypeLits

-- | \(p\)-adic numbers \({\Bbb Q}_p\), for prime \(p\)
data PAdic (p::Nat) = PAS !Int (PowerSeries Rational)
-- p-adic series
-- denominator a `mod` p /= 0

-- field operations on p-adic series

instance KnownNat p => AdditiveMonoid (PAdic p) where
    zero = PAS 0 0
    PAS v1 xs1 + PAS v2 xs2
      | v1 < v2 = PAS v1 (xs1 + shift (v2 - v1) xs2)
      | otherwise = PAS v2 (shift (v1 - v2) xs1 + xs2)
    atimes n (PAS v xs) = PAS v (atimes n xs)

instance KnownNat p => AbelianGroup (PAdic p) where
    negate (PAS v xs) = PAS v (- xs)
    gtimes n (PAS v xs) = PAS v (gtimes n xs)

instance KnownNat p => Semiring (PAdic p) where
    one = PAS 0 1
    PAS v1 xs1 * PAS v2 xs2 = PAS (v1 + v2) (xs1 * xs2)
    fromNatural n = PAS 0 (fromNatural n)

instance KnownNat p => Ring (PAdic p) where
    fromInteger n = PAS 0 (fromInteger n)

instance KnownNat p => DivisionSemiring (PAdic p) where
    recip pas = PAS (-v) (invert xs)
      where
        PAS v xs = invertible pas

-- inverse of an invertible power series (first term non-zero)
invert :: Field a => PowerSeries a -> PowerSeries a
invert xs = mapAdditive (/ x) (recipSimple (mapAdditive (/ x) xs))
  where
    x = atZero xs

-- invertible equivalent p-adic series: leading term has valuation 0
invertible :: KnownNat p => PAdic p -> PAdic p
invertible pas@(PAS v0 xs0) = invertibleAux v0 xs0
  where
    p = natVal pas
    invertibleAux v xs
      | x == 0 = invertibleAux (v+1) xs'
      | r == 0 = invertibleAux (v+1) (constant (q % denominator x) + xs')
      | otherwise = PAS v xs
      where
        x = atZero xs
        xs' = divX xs
        (q, r) = numerator x `divMod` p

instance KnownNat p => Semifield (PAdic p)
instance KnownNat p => DivisionRing (PAdic p)
instance KnownNat p => Field (PAdic p)

-- The unique field homomorphism from the rationals to \({\Bbb Q}_p\)
instance KnownNat p => FromRational (PAdic p) where
    fromRational = toPAdic

toPAdic :: KnownNat p => Rational -> PAdic p
toPAdic x = pas
  where
    pas = PAS (- k_n) (constant (numerator x % n))
    (k_n, n) = value p (denominator x)
    p = natVal pas

value :: Integer -> Integer -> (Int, Integer)
value p n
  | r == 0 = (k+1, n')
  | otherwise = (0, n)
  where
    (q, r) = n `divMod` p
    (k, n') = value p q

-- | \(p\)-adic integers \({\Bbb Z}_p\), for prime \(p\)
newtype PAdicInteger p = PAI (PAdic p) -- v >= 0

instance KnownNat p => AdditiveMonoid (PAdicInteger p) where
    zero = PAI zero
    PAI as1 + PAI as2 = PAI (as1 + as2)
    atimes n (PAI as) = PAI (atimes n as)

instance KnownNat p => AbelianGroup (PAdicInteger p) where
    negate (PAI as) = PAI (negate as)
    gtimes n (PAI as) = PAI (gtimes n as)

instance KnownNat p => Semiring (PAdicInteger p) where
    one = PAI one
    PAI as1 * PAI as2 = PAI (as1 * as2)
    fromNatural n = PAI (fromNatural n)

instance KnownNat p => Ring (PAdicInteger p) where
    fromInteger n = PAI (fromInteger n)

-- | Units have valuation 0.
-- Standard associates have the form \(p^k\) for non-negative \(k\).
instance KnownNat p => StandardAssociate (PAdicInteger p) where
    stdAssociate (PAI pas) = case invertible pas of
       PAS v _ -> PAI (PAS v 1)
    stdUnit (PAI pas) = case invertible pas of
       PAS _ as -> PAI (PAS 0 as)
    stdRecip (PAI pas) = case invertible pas of
       PAS _ as -> PAI (PAS 0 (invert as))

-- | Embedding of \(p\)-adic integers into \(p\)-adic numbers
fromPAdicInteger :: PAdicInteger p -> PAdic p
fromPAdicInteger (PAI x) = x

-- | Infinite list of digits \( 0 \leq d < p \).
digits :: KnownNat p => PAdicInteger p -> [Int]
digits pai@(PAI (PAS v as)) = replicate v 0 ++ norm (natVal pai) as

norm :: Integer -> PowerSeries Rational -> [Int]
norm p xs = case normStep p x of
    (a, x') -> a : norm p (constant x' + xs')
  where
    x = atZero xs
    xs' = divX xs

normStep :: Integer -> Rational -> (Int, Rational)
normStep p x
  | m `mod` p == 0 = (0, (m `div` p) % n)
  | otherwise = case (m*recip_n) `divMod` p of
    (q, r) -> (fromInteger r, (q*n + m*recip_p) % n)
  where
    m = numerator x
    n = denominator x
    (recip_n, recip_p) = bezout n p

-- | The \(p\)-adic integer obtained by substituting \(p\) for the
-- indeterminate of the power series.
pAdicInteger :: (Integral a, KnownNat p) => PowerSeries a -> PAdicInteger p
pAdicInteger as = PAI (PAS 0 (mapAdditive fromIntegral as))

-- | Split a \(p\)-adic number as \(\frac{x}{p^k}\)
-- for the least \( k \geq 0 \) such that \(x\) is a \(p\)-adic integer.
fromPAdic :: KnownNat p => PAdic p -> (Int, PAdicInteger p)
fromPAdic (PAS v0 as0) = fp v0 as0
  where
    fp v as
      | v >= 0 = (0, PAI (PAS v as))
      | atZero as == 0 = fp (v+1) (divX as)
      | otherwise = (v, PAI (PAS 0 as))

mulP :: PAdicInteger p -> PAdicInteger p
mulP (PAI (PAS v as)) = PAI (PAS (v+1) as)

-- | The square root of an integer \(n\) as a \(p\)-adic integer, if
-- it exists.
--
-- * For odd \(p\), the square root exists if and only if \(n\) is
--   zero or of the form \(p^{2k}m\) where \(m\) is a quadratic residue
--   modulo \(p\) not divisible by \(p\).
--
-- * For \(p = 2\), the square root exists if and only if \(n\) is zero
--   or of the form \(p^{2k}m\) where \(m\) is equivalent to 1 modulo 8.
--
-- Thus some positive integers will not have square roots, but some
-- negative integers will.
--
-- The lexically least square root is returned.  Its negation will also
-- be a square root of \(n\).
maybeSqrt :: KnownNat p => Integer -> Maybe (PAdicInteger p)
maybeSqrt a
  | a == 0 = Just 0
  | a `mod` (p*p) == 0 = fmap mulP (maybeSqrt (p `div` (p*p)))
  | a `mod` p == 0 = Nothing
  | p == 2 && a `mod` 8 == 1 = Just (pai (expand2 a 1))
  | p == 2 = Nothing
  | otherwise = mb_pas
  where
    mb_pas = fmap (pai . expandOdd p a) mb_r1
    mb_r1 = listToMaybe [r | r <- [1..p `div` 2], (a - r*r) `mod` p == 0]
    p = natVal (fromJust mb_pas)
    pai = PAI . PAS 0 . fromCoefficients . map fromIntegral

expandOdd :: Integer -> Integer -> Integer -> [Int]
expandOdd p a r1 = fromInteger r1 : aux p r1
  where
    aux pk r = fromInteger t : aux (p*pk) (r + t*pk)
      where
        recip_d = fst (bezout (2*r) p)
        t = (a - r*r) `div` pk * recip_d `mod` p

expand2 :: Integer -> Integer -> [Int]
expand2 a r1 = fromInteger r1 : aux 2 r1
  where
    aux pk r = fromInteger t : aux (2*pk) (r + t*pk)
      where
        t = (a - r*r) `div` (2*pk) `mod` 2
