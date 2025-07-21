{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.PowerSeries.General
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: formal power series
-- generalized to arbitrary exponents.
--
-----------------------------------------------------------------------------

module Data.YAP.PowerSeries.General (
    -- * General power series
    PowerSeries,
    -- * Construction
    term,
    constant,
    identity,
    fromTerms,
    fromCoefficients,
    -- * Queries
    order,
    terms,
    -- * Special cases
    LaurentSeries,
    laurentSeries,
    LeviCivitaField,
    ) where

import Prelude.YAP
import Data.YAP.Algebra

-- | A formal series of the form
--
-- \[
-- \sum_{e \in I} a_e x^e
-- \]
--
-- such that the set of indices \(e\) for which \(a_e\) is non-zero is
-- /left-finite/: for any \(i\), the set of indices \(e < i\) for which
-- \(a_e\) is non-zero is finite.
--
-- Addition of indices is required to preserve the ordering.
newtype PowerSeries i a = PS [(i, a)]

instance AdditiveFunctor (PowerSeries i) where
    mapAdditive f (PS as) = PS (map (fmap f) as)

-- | fails for equal series
instance (Eq i, Eq a) => Eq (PowerSeries i a) where
    PS xs == PS ys = (xs ++ padding) == (ys ++ padding)
      where
        padding = error "comparison of equal series"

-- | treats the indeterminate as a positive infinitesimal
instance (Ord i, Ord a, AdditiveMonoid a) => Ord (PowerSeries i a) where
    compare (PS xs) (PS ys) = comp xs ys

comp :: (Ord i, Ord a, AdditiveMonoid a) => [(i, a)] -> [(i, a)] -> Ordering
comp [] [] = error "comparison of equal series"
comp ((_, vx):_) [] = compare vx zero
comp [] ((_, vy):_) = compare zero vy
comp ((ix, vx):xs) ((iy, vy):ys) = case compare ix iy of
    LT -> compare vx zero
    EQ -> compare vx vy <> comp xs ys
    GT -> compare zero vy

instance (Show i, Show a, Eq a, AdditiveMonoid a) =>
        Show (PowerSeries i a) where
    showsPrec p xs =
        showParen (p > 10) $ showString "fromTerms " . shows (terms xs)

-- | Construct a power series from a list in ascending order of index
--
-- prop> fromTerms ts = sum [term i a | (i, a) <- ts]
fromTerms :: (Eq a, AdditiveMonoid a) => [(i, a)] -> PowerSeries i a
fromTerms = PS . dropZeroes

dropZeroes :: (Eq a, AdditiveMonoid a) => [(i, a)] -> [(i, a)]
dropZeroes xs = [(i, v) | (i, v) <- xs, v /= zero]

-- | @'term' i a@ is a series consisting of the term \(a x^i\).
--
-- prop> term i a * term j b = term (i+j) (a*b)
term :: (Eq a, AdditiveMonoid a) => i -> a -> PowerSeries i a
term i a
  | a == zero = PS []
  | otherwise = PS [(i, a)]

-- | Identity function, i.e. the indeterminate \(x\)
--
-- prop> identity = term 1 1
identity :: (Semiring i, Semiring a) => PowerSeries i a
identity = PS [(one, one)]

-- | Power series representing a constant value \(c\)
--
-- prop> constant a = term 0 a
constant :: (AdditiveMonoid i, Eq a, AdditiveMonoid a) => a -> PowerSeries i a
constant = term zero

-- | Power series formed from a list of coefficients of indices 0, 1, ...
-- If the list is finite, the remaining coefficients are zero.
fromCoefficients :: (Semiring i, Eq a, AdditiveMonoid a) =>
    [a] -> PowerSeries i a
fromCoefficients = fromTerms . zip (iterate (+one) zero)

-- | A formal power series with integer indices, of which finitely many
-- are negative.
type LaurentSeries = PowerSeries Integer

-- | A Laurent series with coefficients starting from the given index
laurentSeries :: (Eq a, AdditiveMonoid a) => Integer -> [a] -> LaurentSeries a
laurentSeries i0 = fromTerms . zip [i0..]

-- | The Levi-Civita field.
type LeviCivitaField = PowerSeries Rational

-- | The smallest exponent with a non-zero coefficient (undefined on 'zero')
order :: (Eq a, AdditiveMonoid a) => PowerSeries i a -> i
order (PS as) = case dropZeroes as of
    [] -> error "order of a zero series"
    (i, _):_ -> i

-- | Indices with non-zero coefficients, in ascending order
terms :: (Eq a, AdditiveMonoid a) => PowerSeries i a -> [(i, a)]
terms (PS as) = dropZeroes as ++ error "terms of a zero series"

-- | Pointwise addition
instance (Ord i, Eq a, AdditiveMonoid a) =>
        AdditiveMonoid (PowerSeries i a) where
    PS xs + PS ys = PS (add xs ys)
    zero = PS []
    atimes n xs
      | n == zero = zero
      | otherwise = mapAdditive (atimes n) xs

add :: (Ord i, Eq a, AdditiveMonoid a) => [(i, a)] -> [(i, a)] -> [(i, a)]
add [] ys = ys
add xs [] = xs
add xs@((ix, vx):xs') ys@((iy, vy):ys') = case compare ix iy of
    LT -> (ix, vx):add xs' ys
    EQ
      | vxy == zero -> add xs' ys'
      | otherwise -> (ix, vxy):add xs' ys'
      where
        vxy = vx + vy
    GT -> (iy, vy):add xs ys'

instance (Ord i, Eq a, AbelianGroup a) =>
        AbelianGroup (PowerSeries i a) where
    negate = mapAdditive negate
    gtimes n xs
      | n == zero = zero
      | otherwise = mapAdditive (gtimes n) xs

-- | Discrete convolution
instance (Ord i, AdditiveMonoid i, Eq a, Semiring a) =>
        Semiring (PowerSeries i a) where
    PS xs * PS ys = fromTerms (mul xs ys)
    one = PS [(zero, one)]
    fromNatural n = constant (fromNatural n)

mul :: (Ord i, AdditiveMonoid i, Eq a, Semiring a) => [(i, a)] -> [(i, a)] -> [(i, a)]
mul ((ix, vx):xs') ys@((iy, vy):ys') =
    (ix + iy, vx*vy) :
        add [(ix + iy', vx * vy') | (iy', vy') <- ys'] (mul xs' ys)
mul _ _ = []

instance (Ord i, AdditiveMonoid i, Eq a, Ring a) => Ring (PowerSeries i a) where
    fromInteger n = constant (fromInteger n)

instance (Ord i, AdditiveMonoid i, Eq a, FromRational a) =>
        FromRational (PowerSeries i a) where
    fromRational x = constant (fromRational x)

instance (Ord i, AbelianGroup i, Eq a, Field a) =>
        DivisionSemiring (PowerSeries i a) where
    recip (PS xs) = fromTerms (inv xs)

inv :: (Ord i, AbelianGroup i, Eq a, Field a) => [(i, a)] -> [(i, a)]
inv [] = error "inv of zero"
inv ((ix, vx):xs) = ys
  where
    ys = (negate ix, recip vx) :
        [(iz - ix, negate (vz / vx)) | (iz, vz) <- mul xs ys]

instance (Ord i, AbelianGroup i, Eq a, Field a) => Semifield (PowerSeries i a)

instance (Ord i, AbelianGroup i, Eq a, Field a) =>
        DivisionRing (PowerSeries i a)

instance (Ord i, AbelianGroup i, Eq a, Field a) => Field (PowerSeries i a)
