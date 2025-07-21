{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.WeylAlgebra
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: Weyl algebras.
--
-----------------------------------------------------------------------------

module Data.YAP.WeylAlgebra (
    -- * Weyl algebras
    Weyl,
    -- * Construction
    fromPolynomial,
    diff,
    fromCoefficients,
    -- * Queries
    order,
    coefficients,
    evaluate,
    evaluateWith,
  ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Polynomial (Polynomial)
import qualified Data.YAP.Polynomial as P
import Data.YAP.Utilities.List

-- | The (first) Weyl algebra over @a@, consisting of differential
-- operators of the form
-- \[
-- p_0(x) + p_1(x) \partial_x + \cdots + p_n(x) \partial_x^n
-- \]
-- where each \(p_i(x)\) is a polynomial in \(x\) and each \(\partial_x^i\)
-- is the differentiation operator with respect to \(x\) repeated \(i\) times.
newtype Weyl a = Weyl [Polynomial a]

instance AdditiveFunctor Weyl where
    mapAdditive f (Weyl as) = Weyl (map (mapAdditive f) as)

instance (Eq a, AdditiveMonoid a) => Eq (Weyl a) where
    Weyl as == Weyl bs = eq as bs
      where
        eq [] ys = allZero ys
        eq xs [] = allZero xs
        eq (x:xs) (y:ys) = x == y && eq xs ys

allZero :: (Eq a, AdditiveMonoid a) => [a] -> Bool
allZero = all (== zero)

instance (Ord a, AdditiveMonoid a) => Ord (Weyl a) where
    compare (Weyl as) (Weyl bs) = cmp as bs
      where
        cmp [] [] = EQ
        cmp [] (y:ys) = compare zero y <> cmp [] ys
        cmp (x:xs) [] = compare x zero <> cmp xs []
        cmp (x:xs) (y:ys) = compare x y <> cmp xs ys

instance (Eq a, Show a, AdditiveMonoid a) => Show (Weyl a) where
    showsPrec p x =
        showParen (p > 10) $
            showString "fromCoefficients " . shows (coefficients x)

-- | Pointwise addition
instance (AdditiveMonoid a) => AdditiveMonoid (Weyl a) where
    Weyl xs + Weyl ys = Weyl (add xs ys)
    zero = Weyl []
    atimes n p
      | n == zero = zero
      | otherwise = mapAdditive (atimes n) p

add :: (AdditiveMonoid a) => [Polynomial a] -> [Polynomial a] -> [Polynomial a]
add = longZipWith (+)

-- | Pointwise negation
instance (AbelianGroup a) => AbelianGroup (Weyl a) where
    negate = mapAdditive negate
    gtimes n p
      | n == zero = zero
      | otherwise = mapAdditive (gtimes n) p

-- | Composition of operators
instance (Semiring a) => Semiring (Weyl a) where
    Weyl xs * Weyl ys = Weyl (mul xs ys)
    one = Weyl [one]
    fromNatural i
      | i == zero = zero
      | otherwise = Weyl [fromNatural i]

mul :: (Semiring a) => [Polynomial a] -> [Polynomial a] -> [Polynomial a]
mul as bs = foldl add [] (zipWith (map . (*)) as cs)
  where
    derivatives = iterate (map derivative) bs
    -- Pascal's triangle of binomial coefficients
    pascal = iterate next_row [1]
    next_row ns = zipWith (+) (0:ns) (ns ++ [0::Int])
    -- D^n P = PD^n + nP'D^{n-1} + nC2 P''D^{n-2} + ... + n P^(n-1)D + P^(n)
    cs = [foldl1 add_shift (zipWith (map . atimes) ns derivatives) |
        ns <- pascal]
    add_shift x y = add (zero:x) y

instance (Ring a) => Ring (Weyl a) where
    fromInteger i
      | i == 0 = zero
      | otherwise = Weyl [fromInteger i]

instance (FromRational a) => FromRational (Weyl a) where
    fromRational i
      | i == 0 = zero
      | otherwise = Weyl [fromRational i]

-- | Construct an operator from a list of coefficients of the iterated
-- differential operators in order of increasing number of iterated
-- derivatives.
fromCoefficients :: [Polynomial a] -> Weyl a
fromCoefficients as = Weyl as

-- | Operator representing multiplication by a polynomial
fromPolynomial :: Polynomial a -> Weyl a
fromPolynomial p = Weyl [p]

-- | Derivative operator, i.e. \(\partial_x\), satisfying
--
-- * @'diff'*'fromPolynomial' p = 'fromPolynomial' p*'diff' + 'fromPolynomial' ('derivative' p)@
--
diff :: (Semiring a) => Weyl a
diff = Weyl [zero, one]

-- | Coefficients of the iterated differential operators in order of
-- increasing number of iterations, and with no trailing zeros.
coefficients :: (Eq a, AdditiveMonoid a) => Weyl a -> [Polynomial a]
coefficients = reverse . rev_coefficients

rev_coefficients :: (Eq a, AdditiveMonoid a) => Weyl a -> [Polynomial a]
rev_coefficients (Weyl as) = dropWhile (== zero) (reverse as)

-- | The order of a differential operator.
order :: (Eq a, AdditiveMonoid a) => Weyl a -> Int
order w = max 0 (length (rev_coefficients w) - 1)

-- | Evaluate an operator on a given polynomial.
evaluate :: (Semiring a) => Weyl a -> Polynomial a -> Polynomial a
evaluate (Weyl as) p = sum (zipWith (*) as (iterate derivative p))

-- | Evaluate an operator, given embeddings of values and the identity
-- polynomial.
evaluateWith :: (Eq a, AdditiveMonoid a, Differentiable b) =>
    Weyl a -> (a -> b) -> b -> b -> b
evaluateWith (Weyl as) from_const ident f =
    sum (zipWith (*) (map from_poly as) (iterate derivative f))
  where
    from_poly p =
        foldr (\ a v -> from_const a + ident*v) zero (P.coefficients p)
