{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.FiniteMap
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: the monoid, group,
-- semiring or ring of functions with finite support (i.e. mapping
-- finitely inputs to non-zero outputs), or equivalently a free module
-- extended to @a@ with multiplication by convolution.
-- 
-- These functions may be interpreted as generalized formal polynomials,
-- mapping exponents to corresponding coefficients (a monoid algebra).
--
-----------------------------------------------------------------------------

module Data.YAP.FiniteMap (
    -- * Functions with finite support
    FiniteMap,
    mapIndices,
    mapCoefficients,
    -- * Construction
    constant,
    primitive,
    fromAssocs,
    -- * Queries
    find,
    assocs,
    evaluateWith,
    -- * Basic applications
    Multiset,
    FreeRing,
    -- * Additive monoids: generalized polynomials
    GenPolynomial,
    primitiveMonomial,
    -- ** Polynomials in one indeterminate
    UniPolynomial,
    LaurentPolynomial,
    -- ** Polynomials in multiple indeterminates
    MultiPolynomial,
    indeterminate,
    prettyMultiPolynomial,
    prettyMultiPolynomialOn,
    evaluate,
    -- ** Indexed indeterminates
    Xs(..),
    allXs,
    prettyXs,
    pretty,

    -- ** Partition polynomials
    -- $partition_polynomials

    ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.MonoidAdaptors
import Data.YAP.Polynomial (Polynomial)
import qualified Data.YAP.Polynomial as Poly
import Data.YAP.Utilities.List as List

import Data.List (intersperse, sort, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (Down(..))
import Numeric.Natural

-- | A function with finite support to an additive monoid,
-- i.e. mapping all but a finite number of inputs to 'zero'.
-- 
-- The special case where the element type @a@ is the two-element
-- Boolean semiring is equivalent to "Data.YAP.FiniteSet".
newtype FiniteMap i a = M (Map i a)
    deriving (Eq, Ord)
-- Invariant: values in the map are non-zero

-- | A version of `fmap` that is well-defined only if @f x = 'zero'@
-- if and only if @x@ is 'zero'.
unsafeMap :: (a -> b) -> FiniteMap i a -> FiniteMap i b
unsafeMap f (M as) = M (fmap f as)

instance (Show i, Show a) => Show (FiniteMap i a) where
    showsPrec d xs =
        showParen (d > 10) $
            showString "fromAssocs " . shows (assocs xs)

-- | Map the indices of a finite map.
mapIndices :: (Ord j, Eq a, AdditiveMonoid a) =>
    (i -> j) -> FiniteMap i a -> FiniteMap j a 
mapIndices f p = fromAssocs [(f i, a) | (i, a) <- assocs p]

-- | Map the coefficients of a finite map.
mapCoefficients :: (Eq b, AdditiveMonoid b) =>
    (a -> b) -> FiniteMap i a -> FiniteMap i b
mapCoefficients f (M as) = M (Map.filter (/= zero) (fmap f as))

-- | Composite value
--
-- prop> fromAssocs ts = sum [primitive i * constant a | (i, a) <- ts]
--
fromAssocs :: (Ord i, Eq a, AdditiveMonoid a) => [(i, a)] -> FiniteMap i a
fromAssocs xs = M (Map.filter (/= zero) (Map.fromListWith (+) xs))

singleton :: (Eq a, AdditiveMonoid a) => i -> a -> FiniteMap i a
singleton i x
  | x == zero = M Map.empty
  | otherwise = M (Map.singleton i x)

-- | An injective map preserving addition and 'zero' (and multiplication
-- and 'one', if defined).
constant :: (Monoid i, Eq a, AdditiveMonoid a) => a -> FiniteMap i a
constant = singleton mempty

-- | A singleton map with value 'one'. Satisfies:
--
-- prop> one = primitive mempty
-- prop> primitive i * primitive j = primitive (i <> j)
-- prop> primitive i * constant a = constant a * primitive i
--
primitive :: (Semiring a) => i -> FiniteMap i a
primitive i = M (Map.singleton i one)

-- | Find the value at a given key.
find :: (Ord i, AdditiveMonoid a) => FiniteMap i a -> i -> a
find (M m) i = Map.findWithDefault zero i m

-- | Values of the support with their mappings.
assocs :: FiniteMap i a -> [(i, a)]
assocs (M xs) = Map.assocs xs

-- | Sum the valuations of the terms of a finite map.
--
-- prop> evaluateWith primitive constant = id
-- prop> evaluateWith f g (primitive i) = f i
-- prop> evaluateWith f g (constant a) = g a
--
evaluateWith :: (Semiring b) => (i -> b) -> (a -> b) -> FiniteMap i a -> b
evaluateWith f g m = sum [f i * g a | (i, a) <- assocs m]

-- | Pointwise addition
instance (Ord i, Eq a, AdditiveMonoid a) =>
        AdditiveMonoid (FiniteMap i a) where
    M xs + M ys = M (Map.filter (/= zero) (Map.unionWith (+) xs ys))
    zero = M Map.empty
    atimes n m
      | n == zero = zero
      | otherwise = unsafeMap (atimes n) m

instance (Ord i, Eq a, AbelianGroup a) =>
        AbelianGroup (FiniteMap i a) where
    negate = unsafeMap negate
    gtimes n m
      | n == zero = zero
      | otherwise = unsafeMap (gtimes n) m

-- | Discrete convolution
instance (Ord i, Monoid i, Eq a, Semiring a) =>
        Semiring (FiniteMap i a) where
    xs * ys =
        foldb (+) zero
            [singleton (x <> y) (xv * yv) |
                (x, xv) <- assocs xs, (y, yv) <- assocs ys]
    one = M (Map.singleton mempty one)
    fromNatural n = constant (fromNatural n)

{-
In particular,

singleton x xv * singleton y yv = singleton (x <> y) (xv * yv)

which, combined with distributivity, implies that multiplication is
discrete convolution.
-}

instance (Ord i, Monoid i, Eq a, Ring a) => Ring (FiniteMap i a) where
    fromInteger n = constant (fromInteger n)

instance (Ord i, Monoid i, Eq a, FromRational a) =>
        FromRational (FiniteMap i a) where
    fromRational x = constant (fromRational x)

-- General monoids

-- | Multisets or bags (free commutative monoids)
--
-- These support addition (as multiset union) but not multiplication.
-- 'primitive' constructs singleton multisets.
--
-- Replacing 'Numeric.Natural.Natural' with 'Integer' would yield free
-- Abelian groups.
type Multiset a = FiniteMap a Natural

-- | The free ring (or semiring) generated by non-commuting variables @v@
-- and ring @a@.
type FreeRing v a = FiniteMap [v] a

-- Additive monoids, yielding polynomials

-- | A generalized polynomial with primitive monomials indexed by type
-- @i@ and coefficients of type @a@.
-- Multiplication is commutative.
--
-- 'constant' constructs a constant.
type GenPolynomial i a = FiniteMap (Sum i) a

-- | A primitive monomial: a term with coefficient 'one'.
--
-- prop> primitiveMonomial zero = one
-- prop> primitiveMonomial (i+j) = primitiveMonomial i * primitiveMonomial j
--
primitiveMonomial ::
    (Ord i, AdditiveMonoid i, Semiring a) => i -> GenPolynomial i a
primitiveMonomial i = primitive (Sum i)

-- | Semiring (or ring) of ordinary polynomials in one indeterminate.
type UniPolynomial a = GenPolynomial Natural a

-- | Semiring (or ring) of Laurent polynomials in one indeterminate.
type LaurentPolynomial a = GenPolynomial Integer a

-- | An implementation of semirings (or rings) of polynomials in multiple
-- indeterminates, using a multiset to record the multiplicity of each
-- indeterminate.
type MultiPolynomial v a = GenPolynomial (Multiset v) a

-- | A multivariate polynomial consisting of a single indeterminate
indeterminate :: (Semiring a) => v -> MultiPolynomial v a
indeterminate = primitive . Sum . primitive

-- | An infinite type of indexed indeterminates
newtype Xs = X Natural
    deriving (Eq, Ord, Read, Show)

-- | The list of indeterminates @[X 1, X 2, X 3, ...]@
allXs :: (Semiring a) => [MultiPolynomial Xs a]
allXs = map (indeterminate . X) (iterate (+one) one)

-- | Concise display of 'Xs' as @x@/i/
prettyXs :: Xs -> String
prettyXs (X i) = 'x':show i

-- | Pretty-print a polynomial in 'Xs', with the terms in the order used
-- by Abrabowitz and Stegun /Handbook of Mathematical Functions/ p. 831:
-- first by number of variables and then in lexicographical order (both
-- assuming powers expanded).
pretty :: (Eq a, Show a, Semiring a) => MultiPolynomial Xs a -> String
pretty = prettyMultiPolynomialOn keyAbSt prettyXs
  where
    keyAbSt s = (sum (map snd ies), sort (map (fmap Down) ies))
      where
        ies = assocs s

-- | Pretty-print a multivariate polynomial.
prettyMultiPolynomial :: (Eq a, Show a, Semiring a, Ord v) =>
    (v -> String) -> MultiPolynomial v a -> String
prettyMultiPolynomial showVar p = showTerms showVar 0 (assocs p) ""

-- | Pretty-print a multivariate polynomial given an ordering of monomials
prettyMultiPolynomialOn :: (Eq a, Show a, Semiring a, Ord b, Ord v) =>
    (Multiset v -> b) -> (v -> String) -> MultiPolynomial v a -> String
prettyMultiPolynomialOn key showVar p =
    showTerms showVar 0 (sortOn keyTerm (assocs p)) ""
  where
    keyTerm (Sum x, _) = key x

plusPrec, mulPrec :: Int
plusPrec = 6
mulPrec = 7

showsMultiPolynomial :: (Eq a, Show a, Semiring a, Ord v) =>
    (v -> String) -> Int -> MultiPolynomial v a -> ShowS
showsMultiPolynomial showVar d p = showTerms showVar d (assocs p)

showTerms :: (Eq a, Show a, Semiring a, Ord v) =>
    (v -> String) -> Int -> [(Sum (Multiset v), a)] -> ShowS
showTerms _ _ [] = showChar '0'
showTerms showVar d [t] = showTerm showVar d t
showTerms showVar d ts = showParen (d > plusPrec) $
    List.compose $ intersperse (showString " + ") $
        map (showTerm showVar (plusPrec+1)) ts

showTerm :: (Eq a, Show a, Semiring a, Ord v) =>
    (v -> String) -> Int -> (Sum (Multiset v), a) -> ShowS
showTerm showVar d (vars, a)
  | vars == mempty = showsPrec d a
  | a == one = showFactors showVar d vars
  | otherwise =
        showsPrec (mulPrec+1) a . showChar '*' .
            showFactors showVar mulPrec vars

showFactors :: (v -> String) -> Int -> Sum (Multiset v) -> ShowS
showFactors showVar d (Sum vs) = case assocs vs of
    [f] -> showFactor showVar f
    fs -> showParen (d > mulPrec) $
        List.compose $ intersperse (showChar '*') $ map (showFactor showVar) fs

showFactor :: (v -> String) -> (v, Natural) -> ShowS
showFactor showVar (v, n)
  | n == one = showString (showVar v)
  | otherwise = showString (showVar v) . showString "^" . shows n

-- | Evaluate a multivariate polynomial for an assignment of values
-- to variables.
evaluate :: (Semiring b) => (v -> b) -> (a -> b) -> MultiPolynomial v a -> b
evaluate vval = evaluateWith subsPartition
  where
    subsPartition p = product [vval v^k | (v, k) <- assocs (getSum p)]

{- $partition_polynomials

Primitive monomials correspond to partitions of a natural number \(n\),
with indeterminates \(x_i\) corresponding to parts of size \(i\)
and powers corresponding to multiplicities.  For example, a primitive
monomial \(x_2^3 x_3\) corresponds to a partition of 9 into 3 parts of
size 2 and one of size 3.

The type 'Xs' may be used as indeterminates for the sequence of coefficients
generated by a power series.

* exponential generating function:
  \( \sum_{n=1}^\infty x_n \frac{t^n}{n!} \), generalizing \(x(e^t-1)\)
  (see "Data.YAP.PowerSeries.Maclaurin#g:Multi_variable_sequences")

* logarithmic generating function:
  \( \sum_{n=1}^\infty x_n \frac{t^n}{n} \), generalizing \(x \log \frac{1}{1-t}\)
  (see "Data.YAP.PowerSeries#g:Multi_variable_sequences")

* ordinary generating function:
  \( \sum_{n=1}^\infty x_n t^n \), generalizing \(xt \over 1-t\)
  (see "Data.YAP.PowerSeries#g:Multi_variable_sequences")

-}
