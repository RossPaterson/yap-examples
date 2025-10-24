{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Polynomial
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: formal polynomials.
--
-----------------------------------------------------------------------------

module Data.YAP.Polynomial (
    -- * Polynomials
    Polynomial,
    constant,
    linear,
    fromCoefficients,
    fromRoots,
    RationalFunction,
    -- * Queries
    degree,
    coefficients,
    unsafeCoefficients,
    evaluate,
    pretty,
    -- * Composition
    identity,
    compose,
    -- ** Special compositions
    (.*),
    (.^),
  ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Utilities.List (longZipWith)
import Data.Ratio

import Data.List (intercalate)

infixl 9 .^
infixl 9 .*

-- | Formal polynomials.
newtype Polynomial a = P [a]
    -- ^ Coefficients, least significant first.
    -- There may be trailing zeros, but the interface hides them.

-- | A rational function with coefficients from a field is a field
type RationalFunction a = Ratio (Polynomial a)

instance (Eq a, AdditiveMonoid a) => Eq (Polynomial a) where
    P as == P bs = eq as bs
      where
        eq [] ys = allZero ys
        eq xs [] = allZero xs
        eq (x:xs) (y:ys) = x == y && eq xs ys

allZero :: (Eq a, AdditiveMonoid a) => [a] -> Bool
allZero = all (== zero)

instance (Ord a, AdditiveMonoid a) => Ord (Polynomial a) where
    compare (P as) (P bs) = cmp as bs
      where
        cmp [] [] = EQ
        cmp [] (y:ys) = compare zero y <> cmp [] ys
        cmp (x:xs) [] = compare x zero <> cmp xs []
        cmp (x:xs) (y:ys) = compare x y <> cmp xs ys

instance (Eq a, Show a, AdditiveMonoid a) => Show (Polynomial a) where
    showsPrec p x =
        showParen (p > 10) $
            showString "fromCoefficients " . shows (coefficients x)

instance (AdditiveMonoid a) => AdditiveMonoid (Polynomial a) where
    P xs + P ys = P (add xs ys)
    zero = P []
    atimes n p
      | n == zero = zero
      | otherwise = mapAdditive (atimes n) p

add :: (AdditiveMonoid a) => [a] -> [a] -> [a]
add = longZipWith (+)

instance (AbelianGroup a) => AbelianGroup (Polynomial a) where
    negate = mapAdditive negate
    gtimes n p
      | n == zero = zero
      | otherwise = mapAdditive (gtimes n) p

instance (Semiring a) => Semiring (Polynomial a) where
    P xs * P ys = P (mul xs ys)
    one = constant one
    fromNatural i = constant (fromNatural i)

mul :: (Semiring a) => [a] -> [a] -> [a]
mul [] _ys = []
mul _xs [] = []
mul (x:xs) ys = add (map (x*) ys) (zero:mul xs ys)

instance (Ring a) => Ring (Polynomial a) where
    fromInteger i = constant (fromInteger i)

instance (FromRational a) => FromRational (Polynomial a) where
    fromRational x = constant (fromRational x)

-- | Units are non-sero constants.  If @p@ is non-zero, @'stdUnit' p@
-- is the leading coefficient of @p@ and @'stdAssociate' p@ is monic
-- (i.e. has a leading coefficient of @1@).
instance (Eq a, Field a) => StandardAssociate (Polynomial a) where
    stdAssociate p = case rev_coefficients p of
        [] -> 0
        a:rev_as -> fromCoefficients (reverse (1:map (/a) rev_as))
    stdUnit p = case rev_coefficients p of
        [] -> 1
        a:_ -> constant a
    stdRecip p = case rev_coefficients p of
        [] -> 1
        a:_ -> constant (recip a)

-- | If @b@ is non-zero, @'mod' a b@ has a smaller degree than @b@.
instance (Eq a, Field a) => Euclidean (Polynomial a) where
    divMod a b
      | null bs = error "division by zero"
      | otherwise = (P (reverse d), P (reverse m))
      where
        (d, m) = divModAux n as bs
        as = rev_coefficients a
        bs = rev_coefficients b
        n = length as - length bs

    euclideanNorm = euclideanNorm . degree

divModAux :: (Eq a, Field a) => Int -> [a] -> [a] -> ([a],[a])
divModAux n as _
  | n < 0 = ([], as)
divModAux n (a:as) bs
  | a == 0 = (0:d, m)
  where
    (d, m) = divModAux (n-1) as bs
divModAux n (a:as) bs@(b:bs') = (c:d, m)
  where
    c = a/b
    (d, m) = divModAux (n-1) (sub as (map (c*) bs')) bs
divModAux _ _ _ = error "divModAux: unexpected arguments"

sub :: (AbelianGroup a) => [a] -> [a] -> [a]
sub xs [] = xs
sub (x:xs) (y:ys) = (x-y) : sub xs ys
sub [] _ = error "can't happen"

-- | Construct a polynomial from a list of coefficients,
-- least significant first.
fromCoefficients :: [a] -> Polynomial a
fromCoefficients = P

-- | Polynomial representing a constant value @c@
constant :: a -> Polynomial a
constant a = fromCoefficients [a]

-- | Linear polynomial, i.e. @'constant' a * 'identity'@
linear :: (AdditiveMonoid a) => a -> Polynomial a
linear a = fromCoefficients [zero, a]

-- | A monic polynomial with the given roots (with multiplicity)
fromRoots :: (Ring a) => [a] -> Polynomial a
fromRoots vs = product [fromCoefficients [-v, 1] | v <- vs]

-- | The coefficients of a polynomial, least significant first
-- and with no trailing zeros.
coefficients :: (Eq a, AdditiveMonoid a) => Polynomial a -> [a]
coefficients = reverse . rev_coefficients

-- | The coefficients of a polynomial, least significant first
-- and with an arbitrary number of trailing zeros.  This is only safe
-- to use in contexts where the number of trailing zeros is immaterial.
unsafeCoefficients :: Polynomial a -> [a]
unsafeCoefficients (P as) = as

-- | The coefficients of a polynomial, starting with the most
-- significant non-zero coefficient.
rev_coefficients :: (Eq a, AdditiveMonoid a) => Polynomial a -> [a]
rev_coefficients (P as) = dropWhile (== zero) (reverse as)

-- | The degree of a polynomial: the highest power of the indeterminate.
degree :: (Eq a, AdditiveMonoid a) => Polynomial a -> Int
degree a = max 0 (length (rev_coefficients a) - 1)

-- | Evaluate a polynomial for a given value of @x@.
--
-- @'evaluate' a x = 'zipWith' (*) ('coefficients' a) ('iterate' (*x) 1)@
--
-- (The implementation uses Horner's rule.)
evaluate :: (Semiring a) => Polynomial a -> a -> a
evaluate (P as) x = foldr (\ a v -> a + x*v) zero as

-- other functions

-- | Pretty-print a polynomial, e.g.
--
-- @pretty (fromCoefficients [3, -4, 0, -1, 5]) \"x\" = \"5x^4 - x^3 - 4x + 3\"@
pretty :: (ToInteger a) => Polynomial a -> String -> String
pretty (P as) x =
    case dropWhile ((== 0) . fst) (reverse (zip (map toInteger as) terms)) of
    [] -> "0"
    [(a,_)] -> show a
    (a,t):ats -> showFirst a ++ t ++ showRest ats
  where
    terms = "" : x : [x ++ "^" ++ show n | n <- [(2::Int)..]]
    showFirst a
      | a < 0 = '-':show (negate a)
      | a == 1 = ""
      | otherwise = show a
    showRest [] = ""
    showRest [(a,t)]
      | a < 0 = " - " ++ show (negate a) ++ t
      | a > 0 = " + " ++ show a ++ t
      | otherwise = ""
    showRest ((a,t):ats)
      | a < 0 = " - " ++ show (negate a) ++ t ++ showRest ats
      | a == 1 = " + " ++ t  ++ showRest ats
      | a > 0 = " + " ++ show a ++ t ++ showRest ats
      | otherwise = showRest ats

-- | Identity polynomial, i.e. /x/
identity :: (Semiring a) => Polynomial a
identity = fromCoefficients [zero, one]

-- | Composition of polynomials:
--
-- @'evaluate' ('compose' a b) = 'evaluate' a . 'evaluate' b@
compose :: (Semiring a) => Polynomial a -> Polynomial a -> Polynomial a
compose = evaluate . mapAdditive constant

-- | Maps a function \(f(x)\) to \(f(a x)\), equivalent to composition
-- with @a*'identity'@.
(.*) :: (Semiring a) => Polynomial a -> a -> Polynomial a
P as .* a = P (zipWith (*) as (iterate (*a) one))
 
-- | Maps a function \(f(x)\) to \(f(x^k)\) for positive \(k\), equivalent
-- to composition with @'identity'^k@.
(.^) :: (AdditiveMonoid a) => Polynomial a -> Int -> Polynomial a
P as .^ k
  | k <= 0 = error "non-positive power"
  | k == 1 = P as
  | otherwise = P (intercalate (replicate (k-1) zero) (map pure as))

instance (Semiring a) => Differentiable (Polynomial a) where
    derivative (P []) = P []
    derivative (P (_:as)) = P (zipWith atimes (iterate (+1) (1::Int)) as)

instance (FromRational a) => Integrable (Polynomial a) where
    integral (P as) = P (0 : zipWith (*) (map coeff [1..]) as)
      where
        coeff n = fromRational (1%n)

instance AdditiveFunctor Polynomial where
    mapAdditive f (P as) = P (map f as)
