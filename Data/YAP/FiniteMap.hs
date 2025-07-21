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
    -- * Construction
    constant,
    indeterminate,
    fromAssocs,
    -- * Queries
    find,
    assocs,
    evaluateWith,
    -- * Applications
    Multiset,
    FreeRing,
    -- ** Additive monoids: generalized polynomials
    OrdinaryPolynomial,
    LaurentPolynomial,
    GenPolynomial,
    genIndeterminate,
    prettyGenPolynomial,
    Xs(..),
    prettyXs,

    -- ** Counting partitions: Bell polynomials #Bell_polynomials#
    -- $bell_polynomials

    -- ** Counting integer compositions
    -- $integer_compositions
    ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.MonoidAdaptors
import Data.YAP.Utilities.List as List

import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural

-- | A function with finite support to an additive monoid,
-- i.e. mapping all but a finite number of inputs to 'zero'.
-- 
-- The special case where the element type @a@ is the Boolean semiring
-- is equivalent to "Data.YAP.FiniteSet".
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

-- | Composite value
--
-- prop> fromAssocs ts = sum [indeterminate i * constant a | (i, a) <- ts]
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

-- | A named indeterminate. Satisfies:
--
-- prop> indeterminate mempty = one
-- prop> indeterminate (i <> j) = indeterminate i * indeterminate j
-- prop> indeterminate i * constant a = constant a * indeterminate i
--
indeterminate :: (Semiring a) => i -> FiniteMap i a
indeterminate i = M (Map.singleton i one)

-- | Find the value at a given key.
find :: (Ord i, AdditiveMonoid a) => FiniteMap i a -> i -> a
find (M m) i = Map.findWithDefault zero i m

-- | Values of the support with their mappings.
assocs :: FiniteMap i a -> [(i, a)]
assocs (M xs) = Map.assocs xs

-- | Evaluate a finite map interpreted as a generalized polynomial,
-- given valuations for the indeterminates and coefficients.
--
-- prop> evaluateWith indeterminate constant = id
-- prop> evaluateWith f g (indeterminate i) = f i
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
-- Replacing 'Numeric.Natural.Natural' with 'Integer' would yield free
-- Abelian groups.
type Multiset a = FiniteMap a Natural

-- | The free ring generated by non-commuting variables @v@ and ring @a@.
type FreeRing v a = FiniteMap [v] a

-- Additive monoids, yielding polynomials

-- | Semiring (or ring) of ordinary polynomials in one indeterminate.
type OrdinaryPolynomial a = FiniteMap (Sum Natural) a

-- | Semiring (or ring) of Laurent polynomials in one indeterminate.
type LaurentPolynomial a = FiniteMap (Sum Integer) a

-- | An implementation of semirings (or rings) of polynomials in several
-- indeterminates, using a multiset to record the multiplicity of each
-- indeterminate.
type GenPolynomial v a = FiniteMap (Sum (Multiset v)) a

-- | A polynomial consisting of a single indeterminate
genIndeterminate :: (Semiring a) => v -> GenPolynomial v a
genIndeterminate = indeterminate . Sum . indeterminate

-- | An infinite type of indexed indeterminates
newtype Xs = X Natural
    deriving (Eq, Ord, Show)

-- | Concise display of 'Xs'
prettyXs :: Xs -> String
prettyXs (X i) = 'x':show i

-- | Pretty-print a general polynomial.
prettyGenPolynomial :: (Eq a, Show a, Semiring a, Ord v) =>
    (v -> String) -> GenPolynomial v a -> String
prettyGenPolynomial showVar p = showsGenPolynomial showVar 0 p ""

plusPrec, mulPrec :: Int
plusPrec = 6
mulPrec = 7

showsGenPolynomial :: (Eq a, Show a, Semiring a, Ord v) =>
    (v -> String) -> Int -> GenPolynomial v a -> ShowS
showsGenPolynomial showVar d p = case assocs p of
    [] -> showChar '0'
    [t] -> showTerm showVar d t
    ts -> showParen (d > plusPrec) $
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

{- $bell_polynomials

A more involved example is exponential generating functions for Bell
polynomials, which encode the ways a set of size \(n\) can be partitioned
into \(k\) parts.

Using "Data.YAP.PowerSeries.Maclaurin", an exponential generating
function for the sequence of variables,

\[
\bar x (t) = \sum_{n=1}^\infty x_n \frac{t^n}{n!}
\]

can be defined as

@
xs :: PowerSeries (GenPolynomial Xs Natural)
xs = fromDerivatives (zero:map (genIndeterminate . X) (iterate (+one) one))
@

The exponential generating function for complete Bell polynomials is
obtained by applying the exponential transform to this series:

\[
e^{ \bar x (t) } = 1 + \sum_{n=1}^\infty B_n(x_1,\ldots, x_n) \frac{t^n}{n!}
\]

@
completeBell :: PowerSeries (GenPolynomial Xs Natural)
completeBell = compose expS xs
@

In these polynomials, subscripts denote the size of each part,
superscripts denote the number of parts of that size, and coefficients
denote the number of ways of partitioning \(n\) elements into parts of
those sizes.  For example, the 4th entry is:

>>> (!!4) $ derivatives $ completeBell
fromAssocs [
(Sum (fromAssocs [(X 1,1),(X 3,1)]),4),
(Sum (fromAssocs [(X 1,2),(X 2,1)]),6),
(Sum (fromAssocs [(X 1,4)]),1),
(Sum (fromAssocs [(X 2,2)]),3),
(Sum (fromAssocs [(X 4,1)]),1)]

This encodes the Bell polynomial

\[
	B_4(x_1, x_2, x_3, x_4) =
		4 x_1 x_3 + 6 x_1^2 x_2 + x_1^4 + 3 x_2^2 + x_4
\]

which says that a set of 4 elements may be partitioned
in 4 ways into sets of size 1 and 3,
in 6 ways into 2 sets of size 1 and one of size 2,
in 1 way into 4 sets of size 1, and so on.

Each complete Bell polynomial \(B_n\) is the sum of \(n\) partial Bell
polynomials \(B_{n,k}\) each describing partitions into \(k\) parts:

\[
	B_n(x_1, \ldots, x_n) = \sum_{k=1}^n B_{n,k}(x_1,\ldots,x_{n-k+1})
\]

The exponential generating function for partial Bell polynomials is

\[
e^{ u \bar x (t) } =
	1 + \sum_{n=1}^\infty
		\left( \sum_{k=1}^n B_{n,k}(x_1,\ldots,x_{n-k+1}) u^k \right)
		\frac{t^n}{n!}
\]

@
partialBell :: PowerSeries (Polynomial (GenPolynomial Xs Natural))
partialBell = binomialType xs
@

For example, the 4th entry is:

>>> (!!4) $ derivatives $ partialBell
fromCoefficients [
fromAssocs [],
fromAssocs [(Sum (fromAssocs [(X 4,1)]),1)],
fromAssocs [(Sum (fromAssocs [(X 1,1),(X 3,1)]),4),(Sum (fromAssocs [(X 2,2)]),3)],
fromAssocs [(Sum (fromAssocs [(X 1,2),(X 2,1)]),6)],
fromAssocs [(Sum (fromAssocs [(X 1,4)]),1)]]

This is a polynomial whose \(k\)th coefficient is the
partial Bell polynomial \(B_{4,k}\):

\[ B_{4,1}(x_1, x_2, x_3, x_4) = x_4 \]

\[ B_{4,2}(x_1, x_2, x_3) = 4 x_1 x_3 + 3 x_2^2 \]

\[ B_{4,3}(x_1, x_2) = 6 x_1^2 x_2 \]

\[ B_{4,4}(x_1) = x_1^4 \]

For example, \(B_{4,2}\) describes the ways in which 4 elements can be
divided into 2 parts: 4 ways into parts of sizes 1 and 3, and 3 ways
into 2 parts of size 2.

-}

{- $integer_compositions

A similar construction with ordinary generating functions counts
compositions of a non-negative integer \(n\), or equivalently
segmentations of lists of length \(n\).

Using "Data.YAP.PowerSeries", an ordinary generating
function for the sequence of variables,

\[
\bar x (t) = \sum_{n=1}^\infty x_n t^n
\]

can be defined as

@
xs :: PowerSeries (GenPolynomial Xs Natural)
xs = fromDerivatives (zero:map (genIndeterminate . X) (iterate (+one) one))
@

The counterpart of the complete Bell polynomials is generated
by \( 1 \over 1 - \bar x (t) \).
In these polynomials, subscripts denote the size of each part,
superscripts denote the number of those parts, and coefficients denote
the number of ways of composing \(n\) elements into those parts.
For example, the 4th entry is:

>>> (!!4) $ coefficients $ recipOneMinus `compose` xs
fromAssocs [
(Sum (fromAssocs [(X 1,1),(X 3,1)]),2)
(Sum (fromAssocs [(X 1,2),(X 2,1)]),3)
(Sum (fromAssocs [(X 1,4)]),1)
(Sum (fromAssocs [(X 2,2)]),1)
(Sum (fromAssocs [(X 4,1)]),1)]

which encodes the polynomial

\[
	2 x_1 x_3 + 3 x_1^2 x_2 + x_1^4 + x_2^2 + x_4
\]

which says that 4 may be composed
in 4 ways from 1 and 3 (1+3 and 3+1),
in 3 ways from two 1s and one 2 (1+1+2, 1+2+1 and 2+1+1), 
and in 1 way from four 1s, two 2s or one 4.

>>> (!!4) $ coefficients $ riordan one xs

The counterpart of the partial Bell polynomials is generated
by \( 1 \over 1 - u \bar x (t) \), an example of a Riordan array.
For example, the 4th entry is:

>>>  (!!4) $ coefficients $ riordan one xs
fromCoefficients [
fromAssocs []
fromAssocs [(Sum (fromAssocs [(X 4,1)]),1)]
fromAssocs [(Sum (fromAssocs [(X 1,1),(X 3,1)]),2),(Sum (fromAssocs [(X 2,2)]),1)]
fromAssocs [(Sum (fromAssocs [(X 1,2),(X 2,1)]),3)]
fromAssocs [(Sum (fromAssocs [(X 1,4)]),1)]]

which encodes the polynomials describing the compositions of 1, 2, 3 and 4
numbers respectively: \( x_4 \), \( 2 x_1 x_3 + x_2^2 \), \( 3 x_1^2 x_2 \)
and \( x_1^4 \).
For example, the compositions of two numbers forming 4 are two
compositions of 1 and 3 and one composition of two 2s.

Switching from `FiniteMap` to `Data.YAP.FiniteSet.FiniteSet` would count
integer partitions.

-}
