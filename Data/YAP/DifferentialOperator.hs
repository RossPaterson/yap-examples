{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.DifferentialOperator
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: the semiring of linear
-- differential operators under addition and composition.
--
-----------------------------------------------------------------------------

module Data.YAP.DifferentialOperator (
    -- * Linear differential operators
    DifferentialOperator,
    Weyl,
    multiply,
    diff,
    fromCoefficients,

    -- * Queries
    order,
    coefficients,
    evaluate,
  ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Polynomial (Polynomial)
import Data.YAP.Utilities.List

-- | A linear differential operator of the form
-- \[
-- p_0(x) + p_1(x) \partial_x + \cdots + p_n(x) \partial_x^n
-- \]
-- where each \(p_i(x)\) is a differentiable function in \(x\) and
-- each \(\partial_x^i\) is the differentiation operator with respect
-- to \(x\) repeated \(i\) times.
newtype DifferentialOperator a = Op [a]

-- | The (first) Weyl algebra over @a@, consisting of linear differential
-- operators with polynomial coefficients.
type Weyl a = DifferentialOperator (Polynomial a)

-- | A version of `fmap` that is well-defined only if @f 'zero' = 'zero'@.
unsafeMap :: (a -> b) -> DifferentialOperator a -> DifferentialOperator b
unsafeMap f (Op as) = Op (map f as)

instance (Eq a, AdditiveMonoid a) => Eq (DifferentialOperator a) where
    Op as == Op bs = eq as bs
      where
        eq [] ys = allZero ys
        eq xs [] = allZero xs
        eq (x:xs) (y:ys) = x == y && eq xs ys

allZero :: (Eq a, AdditiveMonoid a) => [a] -> Bool
allZero = all (== zero)

instance (Ord a, AdditiveMonoid a) => Ord (DifferentialOperator a) where
    compare (Op as) (Op bs) = cmp as bs
      where
        cmp [] [] = EQ
        cmp [] (y:ys) = compare zero y <> cmp [] ys
        cmp (x:xs) [] = compare x zero <> cmp xs []
        cmp (x:xs) (y:ys) = compare x y <> cmp xs ys

instance (Eq a, Show a, AdditiveMonoid a) => Show (DifferentialOperator a) where
    showsPrec p x =
        showParen (p > 10) $
            showString "fromCoefficients " . shows (coefficients x)

-- | Pointwise addition
instance (AdditiveMonoid a) => AdditiveMonoid (DifferentialOperator a) where
    Op xs + Op ys = Op (add xs ys)
    zero = Op []
    atimes n p
      | n == zero = zero
      | otherwise = unsafeMap (atimes n) p

add :: (AdditiveMonoid a) => [a] -> [a] -> [a]
add = longZipWith (+)

-- | Pointwise negation
instance (AbelianGroup a) => AbelianGroup (DifferentialOperator a) where
    negate = unsafeMap negate
    gtimes n p
      | n == zero = zero
      | otherwise = unsafeMap (gtimes n) p

-- | Composition of operators
instance (Differentiable a) => Semiring (DifferentialOperator a) where
    Op xs * Op ys = Op (mul xs ys)
    one = Op [one]
    fromNatural i
      | i == zero = zero
      | otherwise = Op [fromNatural i]

mul :: (Differentiable a) => [a] -> [a] -> [a]
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

instance (Differentiable a, Ring a) => Ring (DifferentialOperator a) where
    fromInteger i
      | i == 0 = zero
      | otherwise = Op [fromInteger i]

instance (Differentiable a, FromRational a) => FromRational (DifferentialOperator a) where
    fromRational i
      | i == 0 = zero
      | otherwise = Op [fromRational i]

-- | Construct an operator from a list of coefficients of the iterated
-- differential operators in order of increasing number of iterations.
fromCoefficients :: [a] -> DifferentialOperator a
fromCoefficients as = Op as

-- | Operator representing multiplication by a differentiable function
multiply :: a -> DifferentialOperator a
multiply p = Op [p]

-- | Derivative operator, i.e. \(\partial_x\), satisfying
--
-- * @'diff'*'multiply' p = 'multiply' p*'diff' + 'multiply' ('derivative' p)@
--
diff :: (Semiring a) => DifferentialOperator a
diff = Op [zero, one]

-- | Coefficients of the iterated differential operators in order of
-- increasing number of iterations, and with no trailing zeros.
coefficients :: (Eq a, AdditiveMonoid a) => DifferentialOperator a -> [a]
coefficients = reverse . rev_coefficients

rev_coefficients :: (Eq a, AdditiveMonoid a) => DifferentialOperator a -> [a]
rev_coefficients (Op as) = dropWhile (== zero) (reverse as)

-- | The order of a differential operator.
order :: (Eq a, AdditiveMonoid a) => DifferentialOperator a -> Int
order w = max 0 (length (rev_coefficients w) - 1)

-- | Evaluate an operator on a given differentiable function.
evaluate :: (Differentiable a) => DifferentialOperator a -> a -> a
evaluate (Op as) p = sum (zipWith (*) as (iterate derivative p))
