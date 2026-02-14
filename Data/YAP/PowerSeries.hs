{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.PowerSeries
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: formal power series.
--
-- * M. Douglas McIlroy, "Power series, power serious",
--   /Journal of Functional Programming/ 9:3 (1999) 325-337.
--   <https://www.cs.dartmouth.edu/~doug/powser.html>
--
-- * M. Douglas McIlroy, "The music of streams",
--   /Information Processing Letters/ 77 (2001) 189-195.
--
-----------------------------------------------------------------------------

module Data.YAP.PowerSeries (
    -- * Formal power series
    PowerSeries,
    constant,
    fromPolynomial,
    fromCoefficients,
    fromDerivatives,

    -- * Queries
    atZero,
    coefficients,
    derivatives,
    flatten,
    toPolynomial,
    modulus,
    order,
    distance,

    -- * Approximations
    approximations,
    approximationsWith,
    padeApproximants,

    -- * Composition
    identity,
    compose,
    inverse,
    inverseSimple,
    -- ** Special compositions
    (.*),
    (.^),

    -- * Other transforms
    divX,
    mulX,
    shift,
    recipSimple,
    divSimple,

    -- * Special series
    recipOneMinus,
    expS,
    logRecipOneMinus,
    powerOnePlus,
    euler,
    -- ** Trigonometric functions
    sinS, cosS, secS, tanS, asinS, atanS,
    -- ** Hyperbolic functions
    sinhS, coshS, sechS, tanhS, asinhS, atanhS,

    -- * Continued fractions
    stieltjes,
    jacobi,

    -- * Sequence transforms
    -- ** Binomial transform
    binomialTransform,
    inverseBinomialTransform,

    -- ** Lambert transform
    lambertTransform,
    inverseLambertTransform,

    -- ** Plethystic exponential (Euler transform)
    pexp,
    pexpInteger,
    plog,
    signedPexp,

    -- * Ordinary generating functions
    -- ** Number sequences
    -- $ogfs

    -- ** Linear recurrences
    linearRecurrence,

    -- ** Formal languages
    GradedLanguage,
    string,

    -- * Probability generating functions #PGF#
    -- $pgf
    bernoulliPGF,
    geometricPGF,
    poissonPGF,

    -- * Polynomial sequences #polynomial_sequences#
    -- $polynomial_sequences
    constants,
    monomials,
    riordan,
    delta,

    -- ** Necklace polynomials #necklace_polynomials#
    -- $necklace_polynomials

    -- ** Polynomial sequence transforms
    lambertTransform2,
    inverseLambertTransform2,

    pexp2,
    plog2,

    -- * Multi-variable polynomial sequences #Multi_variable_sequences#
    ordXs,
    logXs,

    -- ** Cycle index polynomials #Cycle_index_polynomials#
    -- *** Major permutation groups
    identityCycleIndices,
    reversalCycleIndices,
    cyclicCycleIndices,
    dihedralCycleIndices,
    symmetricCycleIndices,
    alternatingCycleIndices,

    -- *** Derived groups
    pairCycleIndex,
    orderedPairCycleIndex,

    -- *** Pólya enumeration
    polyaEnumeration,
    equivalenceClasses,

    -- ** Symmetric polynomials
    -- $symmetric_polynomials

    -- ** Counting integer compositions
    -- $integer_compositions

    -- ** Counting noncrossing partitions
    -- $noncrossing_partitions

  ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Classes
import Data.YAP.FiniteMap hiding (constant)
import Data.YAP.FiniteSet
import qualified Data.YAP.Polynomial as Poly
import Data.YAP.Polynomial (Polynomial, RationalFunction)
import Data.YAP.Ratio
import Data.YAP.Utilities.List (longZipWith)

import Data.List (intercalate, tails)
import Numeric.Natural

infixl 9 .^
infixl 9 .*

-- | Formal power series \(\sum_{n=0}^\infty a_n x^n\), represented by the
-- sequence of coefficients \(a_n\) of powers of the indeterminate \(x\).
newtype PowerSeries a = PS [a]
    -- ^ Coefficients, least significant first.

-- | Value of the function at zero
atZero :: (AdditiveMonoid a) => PowerSeries a -> a
atZero (PS []) = zero
atZero (PS (a:_)) = a

-- Horner view: coefficients of powers of x

-- | Discard the constant term and divide by the indeterminate
divX :: PowerSeries a -> PowerSeries a
divX (PS []) = PS []
divX (PS (_:as)) = PS as

-- | Multiply by the indeterminate
mulX :: (AdditiveMonoid a) => PowerSeries a -> PowerSeries a
mulX f = plusMulX zero f

-- | Multiply by the indeterminate and add @a@
plusMulX :: a -> PowerSeries a -> PowerSeries a
plusMulX a (PS as) = PS (a:as)

-- | Shift the power series by \(k\) (which may be negative): multiply
-- by \(x^k\) and discard any terms with negative exponents.
shift :: (AdditiveMonoid a) => Int -> PowerSeries a -> PowerSeries a
shift _ (PS []) = PS []
shift k (PS as)
  | k >= 0 = PS (replicate k zero ++ as)
  | otherwise = PS (drop (-k) as)

-- | The coefficients of the power series, least significant first.
coefficients :: (AdditiveMonoid a) => PowerSeries a -> [a]
coefficients (PS as) = as ++ repeat zero

-- | Power series formed from a list of coefficients.
-- If the list is finite, the remaining coefficients are zero.
fromCoefficients :: (AdditiveMonoid a) => [a] -> PowerSeries a
fromCoefficients = PS

-- Maclaurin view: values of repeated derivatives at zero

instance (Semiring a) => Differentiable (PowerSeries a) where
    derivative (PS []) = PS []
    derivative (PS (_:as)) = PS (zipWith atimes (from (1::Int)) as)

instance (FromRational a) => Integrable (PowerSeries a) where
    integral (PS as) = PS (0:zipWith (*) (map coeff (from 1)) as)
      where
        coeff n = fromRational (1%n)

instance AdditiveFunctor PowerSeries where
    mapAdditive f (PS as) = PS (map f as)

-- | A list whose \(n\)th entry is the value of the \(n\)th derivative at zero.
derivatives :: (Semiring a) => PowerSeries a -> [a]
derivatives p = zipWith atimes factorials (coefficients p)
  where
    factorials = scanl (*) (1::Integer) [1..]

-- | Power series formed from a list of derivatives at zero.
-- If the list is finite, the remaining derivatives are zero.
fromDerivatives :: (FromRational a) => [a] -> PowerSeries a
fromDerivatives as = fromCoefficients (zipWith (*) (map coeff factorials) as)
  where
    coeff n = fromRational (1%n)
    factorials = scanl (*) 1 [1..]

instance (AdditiveMonoid a) => AdditiveMonoid (PowerSeries a) where
    PS as + PS bs = PS (add as bs)
    zero = PS []
    atimes n p
      | n == zero = zero
      | otherwise = mapAdditive (atimes n) p

add :: (AdditiveMonoid a) => [a] -> [a] -> [a]
add = longZipWith (+)

instance (AbelianGroup a) => AbelianGroup (PowerSeries a) where
    negate = mapAdditive negate
    gtimes n p
      | n == zero = zero
      | otherwise = mapAdditive (gtimes n) p

instance (Semiring a) => Semiring (PowerSeries a) where
    PS as * PS bs = PS (mul as bs)
    one = constant one
    fromNatural i = constant (fromNatural i)

-- convolution
mul :: (Semiring a) => [a] -> [a] -> [a]
mul _ [] = []
mul xs (y:ys) = foldr mulOne [] xs
  where
    mulOne x zs = (x*y) : add (map (x*) ys) zs

instance (Ring a) => Ring (PowerSeries a) where
    fromInteger i = constant (fromInteger i)

instance (FromRational a) => FromRational (PowerSeries a) where
    fromRational x = constant (fromRational x)

-- | Units have non-zero leading coefficients.
-- Standard associates are monomials of the form \(x^n\).
-- 'stdUnit' and 'stdRecip' are not defined on zero.
instance (Eq a, Field a) => StandardAssociate (PowerSeries a) where
    stdAssociate = stdAssociateStream
    stdUnit = until ((/= 0) . atZero) divX
    stdRecip f = 1 `exactDiv` stdUnit f

stdAssociateStream :: (Eq a, Semiring a) => PowerSeries a -> PowerSeries a
stdAssociateStream f
  | atZero f /= zero = one
  | otherwise = mulX (stdAssociateStream (divX f))

-- | @'mod' x y@ is non-zero if @y@ has more leading zeros than @x@.
-- See also 'modulus', for the remainder as a polynomial.
instance (Eq a, Field a) => Euclidean (PowerSeries a) where
    divMod f g = fmap fromCoefficients (divModStream f g)
    div = divStream
    mod f g = fromCoefficients (modStream f g)

    euclideanNorm (PS as) = euclideanNorm (length (takeWhile (== 0) as))

divModStream :: (Eq a, Field a) =>
    PowerSeries a -> PowerSeries a -> (PowerSeries a, [a])
divModStream f g
  | atZero g == 0 = (q, atZero f:r)
  | otherwise = (exactDiv f g, [])
  where
    (q, r) = divModStream (divX f) (divX g)

divStream :: (Eq a, Field a) => PowerSeries a -> PowerSeries a -> PowerSeries a
divStream f g
  | atZero g == 0 = divStream (divX f) (divX g)
  | otherwise = exactDiv f g

modStream :: (Eq a, AdditiveMonoid a) => PowerSeries a -> PowerSeries a -> [a]
modStream f g
  | atZero g == zero = atZero f:modStream (divX f) (divX g)
  | otherwise = []

-- | Reduce a nested power series \( \sum_{n=0} p_n(x) y^n \)
-- to a simple power series \( \sum_{n=0} p_n(x) x^n \).
flatten :: (AdditiveMonoid a) => PowerSeries (PowerSeries a) -> PowerSeries a
flatten (PS ps) = foldr add_shifted zero ps
  where
    add_shifted p q = plusMulX (atZero p) (divX p + q)

-- | Polynomial with the first \(n\) coefficients, equivalent to the
-- remainder of division by \(x^n\).
toPolynomial :: (AdditiveMonoid a) => Int -> PowerSeries a -> Polynomial a
toPolynomial n (PS as) = Poly.fromCoefficients (take n as)

-- | The remainder of division by a non-zero power series is a polynomial.
modulus :: (Eq a, AdditiveMonoid a) =>
    PowerSeries a -> PowerSeries a -> Polynomial a
modulus f g = Poly.fromCoefficients (modStream f g)

-- only valid if g0 is non-zero
exactDiv :: (Field a) => PowerSeries a -> PowerSeries a -> PowerSeries a
exactDiv f g = q
  where
    q = plusMulX (f0/g0) (constant (recip g0) * (divX f - q * divX g))
    f0 = atZero f
    g0 = atZero g

-- | Power series representing a constant value \(c\)
constant :: (AdditiveMonoid a) => a -> PowerSeries a
constant a = PS [a]

-- | Polynomial considered as a power series
fromPolynomial :: (AdditiveMonoid a) => Polynomial a -> PowerSeries a
fromPolynomial p = fromCoefficients (Poly.unsafeCoefficients p)

-- | \({1 \over 1-x} = 1 + x + x^2 + \ldots \) (geometric series),
-- converges for \(|x| < 1\).
-- 'derivatives' yields the factorials.
recipOneMinus :: (Semiring a) => PowerSeries a
recipOneMinus = fromCoefficients (repeat one)

-- | \(e^x = 1 + x + \frac{x^2}{2!} + \frac{x^3}{3!} + \ldots\),
-- converges everywhere.  All derivatives are 1.
expS :: (FromRational a) => PowerSeries a
expS = fromDerivatives (repeat one)

-- | \(\log {1 \over 1-x} = - \log (1 - x) = x + \frac{x^2}{2} + \frac{x^3}{3} + \frac{x^4}{4} + \ldots \),
-- converges for \(-1 < x \leq 1\)
logRecipOneMinus :: (FromRational a) => PowerSeries a
logRecipOneMinus = integral recipOneMinus

-- | \( (1 + x)^a = \sum_{n=0}^\infty \binom{a}{n} x^n \) (binomial series),
-- converges for \(|x| < 1\)
powerOnePlus :: (FromRational a) => a -> PowerSeries a
powerOnePlus a = fromDerivatives (scanl (*) 1 (iterate (subtract 1) a))

-- | \(\sin x\), converges everywhere (but faster for smaller \(x\))
sinS :: (FromRational a) => PowerSeries a
sinS = fromDerivatives (cycle [0, 1, 0, -1])

-- | \(\cos x\), converges everywhere (but faster for smaller \(x\))
cosS :: (FromRational a) => PowerSeries a
cosS = fromDerivatives (cycle [1, 0, -1, 0])

-- | \(\tan x\), converges for \(|x| < {\pi \over 2}\)
tanS :: (FromRational a) => PowerSeries a
tanS = sinS * secS

-- | \(1 \over \cos x\), converges for \(|x| < {\pi \over 2}\)
secS :: (FromRational a) => PowerSeries a
secS = recipSimple cosS

-- | \(\sin^{-1} x\), converges for \(|x| \leq 1\)
asinS :: (FromRational a) => PowerSeries a
asinS = integral $ powerOnePlus (-0.5) .* (-1) .^ 2

-- | \(\tan^{-1} x\), converges for \(|x| \leq 1\)
atanS :: (FromRational a) => PowerSeries a
atanS = integral (fromCoefficients (cycle [1, 0, -1, 0]))

-- | \(\sinh x\), converges everywhere (but faster for smaller \(x\))
sinhS :: (FromRational a) => PowerSeries a
sinhS = fromDerivatives (cycle [zero, one])

-- | \(\cos x\), converges everywhere (but faster for smaller \(x\))
coshS :: (FromRational a) => PowerSeries a
coshS = fromDerivatives (cycle [one, zero])

-- | \(\tanh x\), converges for \(|x| < {\pi \over 2}\)
tanhS :: (FromRational a) => PowerSeries a
tanhS = sinhS * sechS

-- | \(1 \over \cosh x\), converges for \(|x| < {\pi \over 2}\)
sechS :: (FromRational a) => PowerSeries a
sechS = recipSimple coshS

-- | \(\sinh^{-1} x\), converges for \(|x| \leq 1\)
asinhS :: (FromRational a) => PowerSeries a
asinhS = integral $ powerOnePlus (-0.5) .^ 2

-- | \(\tanh^{-1} x\), converges for \(|x| < 1\)
atanhS :: (FromRational a) => PowerSeries a
atanhS = integral (fromCoefficients (cycle [one, zero]))

-- | Euler function (<https://oeis.org/A010815 OEIS A010815>), defined as
-- \[
--	\phi(x) = \prod_{k=1}^\infty (1-x^k)
--	= \sum_{k = -\infty}^\infty (-1)^k x^{k(3k+1) \over 2}
-- \]
-- This is a special case of `pexp`.
euler :: (Ring a) => PowerSeries a
euler =
    expand [(sign k, k*(3*k+1) `div` 2) | k <- [0..]] +
    expand [(sign k, k*(3*k-1) `div` 2) | k <- [1..]]

-- expand a list of coefficients and indices (in ascending order of index)
expand :: (AdditiveMonoid a) => [(a, Int)] -> PowerSeries a
expand = fromCoefficients . aux 0
  where
    aux _ [] = []
    aux n ((a, i):ais) = replicate (i-n) zero ++ a : aux (i+1) ais

-- (-1)^k
sign :: (Ring a) => Int -> a
sign k
  | odd k = -1
  | otherwise = 1

-- | The infinite list of evaluations of truncations of the power series.
approximations :: (Semiring a) => PowerSeries a -> a -> [a]
approximations = approximationsWith (*)

-- | The infinite list of evaluations of truncations of the power series,
-- given a function to combine coefficients and powers.
approximationsWith :: (AdditiveMonoid a, Semiring b, AdditiveMonoid c) =>
    (a -> b -> c) -> PowerSeries a -> b -> [c]
approximationsWith f as x =
    scanl (+) zero (zipWith f (coefficients as) (iterate (*x) one))

-- | The list of Padé approximants of \(A(x)\) of order \([m/n]\) such
-- that \(k = m+n\) in order of increasing \(n\).
-- Each approximant is a ratio of polynomials \(P(x)\) and \(Q(x)\)
-- of degrees \(m\) and \(n\) respectively, such that
--
-- \[
-- A(x) \equiv {P(x) \over Q(x)} \pmod{x^{m+n+1}}
-- \]
--
-- The list is obtained by applying the extended Euclidean algorithm
-- to the polynomials \(x^{k+1}\) and \(A_k(x) = A(x) \mod x^{k+1}\)
-- (i.e. selecting the terms up to \(x^k\)), which yields a sequence
-- of equations
--
-- \[
-- P_i(x) = S_i(x) x^{k+1} + Q_i(x) A_k(x)
-- \]
--
padeApproximants :: (Eq a, Field a) =>
    Int -> PowerSeries a -> [RationalFunction a]
padeApproximants k f = [p%q | (_, p, _, q) <- extendedEuclid xk1 truncation]
  where
    truncation = modulus f (fromPolynomial xk1)
    xk1 = Poly.identity^(k+1)

-- | Degree of the first non-zero coefficient.
-- Undefined if the argument is zero.
order :: (Eq a, AdditiveMonoid a) => PowerSeries a -> Int
order f = countSame f zero

-- | Metric on power series (undefined if the arguments are equal)
distance :: (Eq a, AdditiveMonoid a) =>
    PowerSeries a -> PowerSeries a -> Rational
distance f g = 2^^(negate (countSame f g))

countSame :: (Eq a, AdditiveMonoid a) => PowerSeries a -> PowerSeries a -> Int
countSame f g
  | atZero f == atZero g = countSame (divX f) (divX g) + 1
  | otherwise = 0

from :: (Semiring a) => a -> [a]
from = iterate (+one)

-- | Identity function, i.e. the indeterminate
identity :: (Semiring a) => PowerSeries a
identity = mulX one

-- | composition \(f(g(x))\). This is only defined if \(g_0\) is 0.
compose :: (Eq a, Semiring a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries a
compose f g
  | atZero g /= zero =
    error "compose: second series has non-zero constant term"
  | otherwise = composeMulX f (divX g)

-- | Special composition \(f(x g(x))\).
composeMulX :: (Semiring a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries a
composeMulX f g = plusMulX (atZero f) (g * composeMulX (divX f) g)

-- | pre-inverse under 'compose':
--
-- * @'compose' f ('inverse' f) = 'identity'@
--
-- This is only defined if \(f_0\) is zero and \(f_1\) is non-zero.
inverse :: (Eq a, Field a) => PowerSeries a -> PowerSeries a
inverse f
  | atZero f /= 0 = error "inverse: zero constant term"
  | atZero (divX f) == 0 = error "inverse: non-zero linear term"
  | otherwise = unsafeInverse f

-- assumes \(f_0\) is zero and \(f_1\) is non-zero.
unsafeInverse :: (Field a) => PowerSeries a -> PowerSeries a
unsafeInverse f = mulX r
  where
    r = 1 `exactDiv` composeMulX (divX f) r

-- | Special case of 'inverse' that is only valid if the constant term
-- is 0 and the coefficient of the linear term is 1.
inverseSimple :: (Eq a, Ring a) => PowerSeries a -> PowerSeries a
inverseSimple p = mulX r
  where
    r = recipSimple (composeMulX (divX p) r)

-- | Maps a function \(f(x)\) to \(f(a x)\), equivalent to composition
-- with @a*'identity'@.
(.*) :: (Semiring a) => PowerSeries a -> a -> PowerSeries a
PS as .* a = PS (zipWith (*) as (iterate (*a) one))

-- | Maps a function \(f(x)\) to \(f(x^k)\) for positive \(k\), equivalent
-- to composition with @'identity'^k@.
(.^) :: (AdditiveMonoid a) => PowerSeries a -> Int -> PowerSeries a
PS as .^ k
  | k <= 0 = error "non-positive power"
  | k == 1 = PS as
  | otherwise = PS (intercalate (replicate (k-1) zero) (map pure as))

-- | Special case of 'recip' that is only valid if the constant term is 1.
recipSimple :: (Ring a) => PowerSeries a -> PowerSeries a
-- recipSimple p = compose recipOneMinus (1 - p)
recipSimple p = recipOneMinusOf (negate (divX p))

-- | @recipOneMinusOf p = 1/(1 - 'identity'*p)) = 1 + p + p^2 + ...@,
-- but with a less constrained type.
recipOneMinusOf :: (Semiring a) => PowerSeries a -> PowerSeries a
-- recipOneMinusOf p = compose recipOneMinus (mulX p)
recipOneMinusOf p = q
  where
    q = plusMulX one (p*q)

-- | Special case of division that is only valid if the constant term
-- of the divisor is 1.
divSimple :: (Eq a, Ring a) => PowerSeries a -> PowerSeries a -> PowerSeries a
divSimple p q = divOneMinus p (negate (divX q))

-- | @divOneMinus p q = p/(1 - 'identity'*q) = p*(1 + q + q^2 + ...)@,
-- but with a less constrained type.
divOneMinus :: (Semiring a) => PowerSeries a -> PowerSeries a -> PowerSeries a
divOneMinus as bs = q
  where
    q = as + mulX (bs*q)

{- | A Stieltjes fraction
(<https://dlmf.nist.gov/3.10#Px1 Digital Library of Mathematical Functions 3.10>)
generated by a sequence \(a_n\) has the form

\[
    \cfrac{1}{1 - \cfrac{a_0 x}{1 - \cfrac{a_1 x}{1 - \cdots}}}
\]

=== __Examples__

* The Catalan numbers \( C(n) = {(2n)! \over n! (n+1)!} \)
(<https://oeis.org/A000108 OEIS A000108>):

>>> coefficients $ stieltjes $ repeat 1
[1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900,2674440,...

* As the coefficients are repeated, the above is equivalent to a recursive
definition \( C = {1 \over 1-xC} \):

>>> let catalan = recipOneMinus `compose` mulX catalan
>>> coefficients catalan
[1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900,2674440,...

* Double factorials of odd numbers
(<https://oeis.org/A001147 OEIS A001147>):

\[ (2n-1)!! = { (2n)! \over 2^n n! } = 1.3.5. \ldots .(2n-1) \]

>>> coefficients $ stieltjes [1..]
[1,1,3,15,105,945,10395,135135,2027025,34459425,654729075,13749310575,...

* /Bell numbers/, the number of ways to partition \(n\) elements
(<https://oeis.org/A000110 OEIS A000110>):

>>> coefficients $ stieltjes $ concat [[1, n] | n <- [1..]]
[1,1,2,5,15,52,203,877,4140,21147,115975,678570,4213597,27644437,...

-}
stieltjes :: (Semiring a) => [a] -> PowerSeries a
stieltjes as = recipOneMinusOf (foldr divOneMinus zero (map constant as))

{- | A Jacobi fraction
(<https://dlmf.nist.gov/3.10#Px3 Digital Library of Mathematical Functions 3.10>)
generated by sequences \(a_n\) and \(b_n\) has the form

\[
    \cfrac{1}{1 - a_0 x - \cfrac{b_0 x^2}{1 - a_1 x - \cfrac{b_1 x^2}{1 - a_2 x - \cdots}}}
\]

The even part of a Stieltjes fraction is an equivalent Jacobi fraction:

\[
    \cfrac{1}{1 - \cfrac{a_0 x}{1 - \cfrac{a_1 x}{1 - \cfrac{a_2 x}{1 - \cfrac{a_3 x}{1 - \cfrac{a_4 x}{1 - \cdots}}}}}}
    =
    \cfrac{1}{1 - a_0 x - \cfrac{a_0 a_1 x^2}{1 - (a_1+a_2) x - \cfrac{a_2 a_3 x^2}{1 - (a_3+a_4) x - \cdots}}}
\]

=== __Examples__

* Using the above identity, yet another expression for the
/Catalan numbers/ (<https://oeis.org/A000108 OEIS A000108>) is:

>>> coefficients $ jacobi (1:repeat 2) (repeat 1)
[1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900,2674440,...

* Another instance of this identity yields a Jacobi fraction for the
/Bell numbers/ (<https://oeis.org/A000110 OEIS A000110>):

>>> coefficients $ jacobi [1..] [1..]
[1,1,2,5,15,52,203,877,4140,21147,115975,678570,4213597,27644437,...

* /Motzkin numbers/, the number of ways to draw non-intersecting chords
joining \(n\) points on a circle
(<https://oeis.org/A001006 OEIS A001006>):

>>> coefficients $ jacobi (repeat 1) (repeat 1)
[1,1,2,4,9,21,51,127,323,835,2188,5798,15511,41835,113634,310572,...

* As the coefficients are repeated, the above is equivalent to a recursive
definition \( M = {1 \over 1-x(1+xM)} \):

>>> let motzkin = recipOneMinus `compose` mulX (1 + mulX motzkin)
>>> coefficients motzkin
[1,1,2,4,9,21,51,127,323,835,2188,5798,15511,41835,113634,310572,...

* The number of involutions on a set of \(n\) elements
(<https://oeis.org/A000085 OEIS A000085>):

>>> coefficients $ jacobi (repeat 1) [1..]
[1,1,2,4,10,26,76,232,764,2620,9496,35696,140152,568504,...

* /Bessel numbers/, the number of non-overlapping partitions of \(n\)
elements into equivalence classes (<https://oeis.org/A006789 OEIS A006789>):

>>> coefficients $ jacobi [1..] (repeat 1)
[1,1,2,5,14,43,143,509,1922,7651,31965,139685,636712,3020203,...

-}
jacobi :: (Semiring a) => [a] -> [a] -> PowerSeries a
jacobi as bs = foldr fraction zero (zip (as ++ repeat zero) (one:bs))
  where
    fraction (a, b) p = divOneMinus (constant b) (constant a + mulX p)

{- |

If \(A(x)\) is the generating function of the
sequence \( \{a_n\} \), then \( \frac{1}{1-x} A\left( \frac{x}{1-x} \right) \)
is the generating function of the sequence \( \{b_n\} \) where

\[
    b_n = \sum_{k=0}^{n} \binom{n}{k} a_k
\]

For the same transform on sequences from exponential generating functions,
see "Data.YAP.PowerSeries.Maclaurin#g:binomial_transform".

=== __Examples__

* Maximal number of pieces obtained by cutting a circle with \(n\) lines
(<https://oeis.org/A000124 OEIS A000124>).

>>> coefficients $ binomialTransform $ fromCoefficients [1,1,1]
[1,2,4,7,11,16,22,29,37,46,56,67,79,92,106,121,137,154,172,191,211,232,...

* Maximal number of pieces obtained by cutting a sphere with \(n\) planes
(<https://oeis.org/A000125 OEIS A000125>).

>>> coefficients $ binomialTransform $ fromCoefficients [1,1,1,1]
[1,2,4,8,15,26,42,64,93,130,176,232,299,378,470,576,697,834,988,1160,...

* Maximal number of regions obtained by the straight lines joining \(n\)
points around a circle (<https://oeis.org/A000127 OEIS A000127>).

>>> coefficients $ binomialTransform $ fromCoefficients [1,1,1,1,1]
[1,2,4,8,16,31,57,99,163,256,386,562,794,1093,1471,1941,2517,3214,...

-}
binomialTransform :: (Semiring a) => PowerSeries a -> PowerSeries a
binomialTransform a = recipOneMinus * composeMulX a recipOneMinus

{- |
The inverse of `binomialTransform`, namely

\[
    a_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} b_k
\]

is defined by

\[
	A(x) = \frac{1}{1+x} B\left( {x \over 1+x} \right)
\]

For the same transform on sequences from exponential generating functions,
see "Data.YAP.PowerSeries.Maclaurin#g:binomial_transform".

-}
inverseBinomialTransform :: (Ring a) => PowerSeries a -> PowerSeries a
inverseBinomialTransform a = recipOnePlus * composeMulX a recipOnePlus
  where
    recipOnePlus = recipOneMinus .* (-1)

{- |
This transform maps a power series \( A(x) = \sum_{n=1}^\infty a_n x^n\)
(with a zero constant term)
to the Lambert series with the same coefficients:

\[
	B(x)
	= \sum_{n=1}^\infty A(x^n)
	= \sum_{n=1}^\infty a_n \frac{x^n}{1-x^n}
	= \sum_{n=1}^\infty b_n x^n
\]

where \(b_n = \sum_{k \mid n} a_k\).
For the same sum-of-divisors transform on
sequences from Dirichlet generating functions, see
"Data.YAP.DirichletSeries#g:sum_of_divisors_transform".

=== __Examples__

* Number of divisors of \(n\) is generated by the Lambert transform
of \(x \over 1-x\):

>>> coefficients $ lambertTransform $ mulX recipOneMinus
[0,1,2,2,3,2,4,2,4,3,4,2,6,2,4,4,5,2,6,2,...

* Sum of divisors of \(n\) is generated by the Lambert transform
of \(x \over (1-x)^2\):

>>> coefficients $ lambertTransform $ mulX $ derivative recipOneMinus
[0,1,3,4,7,6,12,8,15,13,18,12,28,14,24,24,31,18,39,20,...

-}
lambertTransform :: (AdditiveMonoid a) => PowerSeries a -> PowerSeries a
lambertTransform p = flatten $ mulX $ fromCoefficients [p' .^ k | k <- [1..]]
  where
    p' = divX p

{- |
The inverse of 'lambertTransform' computes the Möbius transform of the
generated sequence, and can be computed from

\[
	A(x) = B(x) - \sum_{n=2}^\infty A(x^n)
\]

provided \(B(x)\) has a zero constant term.
For the same transform on sequences from Dirichlet generating functions,
see "Data.YAP.DirichletSeries#g:moebius_transform".

=== __Examples__

* The Möbius function \( \mu(n) \) (<https://oeis.org/A008683 OEIS A008683>,
see "Data.YAP.DirichletSeries") has the ordinary generating function whose
Lambert transform is \(x\):

>>> coefficients $ inverseLambertTransform identity
[0,1,-1,-1,0,-1,1,-1,0,0,1,-1,0,-1,1,1,0,-1,0,-1,0,1,1,-1,0,...

* The number of numbers less than \(n\) and coprime with \(n\)
(<https://oeis.org/A000010 OEIS A000010>) is the Euler totient
function \( \varphi(n) \), which has the ordinary generating function
whose Lambert transform is \(x \over 1-x\):

>>> coefficients $ inverseLambertTransform $ mulX $ derivative recipOneMinus
[0,1,1,2,2,4,2,6,4,6,4,10,4,12,6,8,8,16,6,18,...

-}
inverseLambertTransform :: (Ring a) => PowerSeries a -> PowerSeries a
inverseLambertTransform q = mulX p'
  where
    p' = divX q - flatten (fromCoefficients (0 : [p' .^ k | k <- [2..]]))

{- |
The plethystic exponential (or Euler transform) of a series \(A(x)\)
with \(a_0 = 0\) is

\[
	PE[A](x)
	= \prod_{k=1}^\infty {1 \over (1 - x^k)^{a_k}}
	= \exp \left( \sum_{k=1}^\infty a_k \log {1 \over (1 - x^k)} \right)
	= \exp \left( \sum_{k=1}^\infty \sum_{n=1}^\infty {a_k x^{nk} \over n} \right)
	= \exp \left( \sum_{n=1}^\infty {A(x^n) \over n} \right)
\]

The product form implies that if the coefficients of \(A(x)\) are
integers, so are the coefficients of \(PE[A](x)\) (and similarly for
non-negative integers), but it doesn't seem possible to prove this to
the type system (see 'pexpInteger').

The exponential name is motivated by the properties

prop> pexp 0 = 1
prop> pexp (f + g) = pexp f * pexp g
prop> pexp (- f) = recip (pexp f)

The effect of this transform on sequences of coefficients can be expressed
applying a Lambert transform to an intermediate sequence:

\[
	C(x)
	= x {d \over dx} \log(PE[A](x))
	= \sum_{n=1}^\infty x {d \over dx} {A(x^n) \over n}
	= \sum_{n=1}^\infty x^n A^\prime(x^n)
\]

The transformation has a combinatorial interpretation.
If \(a_n\) is the number of objects of some kind of size \(n\),
then \(PE[A]\) generates the sequence whose \(n\)th element is the number
of multisets of these objects having total size \(n\).  For example,
any graph is equivalent to a multiset of connected graphs, so if \(a_n\)
is the number of connected graphs on \(n\) nodes, then \(PE[A]\) generates
the sequence whose \(n\)th element is the number of graphs on \(n\) nodes.

-}
pexp :: (Eq a, FromRational a) => PowerSeries a -> PowerSeries a
pexp a = expS `compose` divN (lambertTransform (mulN a))

{- |
The signed plethystic exponential of a series \(A(x)\) with \(a_0 = 0\) is

\[
	PE_{(-)}[A](x)
	= \prod_{k=1}^\infty (1 + x^k)^{a_k}
	= \exp \left( \sum_{k=1}^\infty a_k \log (1 + x^k) \right)
	= \exp \left( \sum_{k=1}^\infty \sum_{n=1}^\infty {(-1)^{n-1} a_k x^{nk} \over n} \right)
	= \exp \left( \sum_{n=1}^\infty {(-1)^{n-1} A(x^n) \over n} \right)
\]

The effect of this transform on sequences of coefficients can be expressed
applying a Lambert transform to an intermediate sequence:

\[
	C(x)
	= x {d \over dx} \log(PE_{(-)}[A](x))
	= \sum_{n=1}^\infty x {d \over dx} {(-1)^{n-1} A(x^n) \over n}
	= \sum_{n=1}^\infty (-1)^{n-1} x^n A^\prime(x^n)
\]

The transformation has a combinatorial interpretation.
If \(a_n\) is the number of objects of some kind of size \(n\),
then \(PE[A]\) generates the sequence whose \(n\)th element is the number
of sets of these objects having total size \(n\).

=== __Example__

The number of ways to partition \(n\) unlabelled elements into parts
of distinct sizes or equivalently the number of partitions into odd parts
(<https://oeis.org/A000009 OEIS A000009>) is generated by

>>> map Data.Ratio.numerator $ coefficients $ signedPexp recipOneMinus
[1,1,1,2,2,3,4,5,6,8,10,12,15,18,22,27,32,38,46,54,64,76,89,104,...

-}
signedPexp :: (Eq a, FromRational a) => PowerSeries a -> PowerSeries a
signedPexp a = expS `compose` divN (signedLambertTransform (mulN a))

signedLambertTransform :: (Ring a) => PowerSeries a -> PowerSeries a
signedLambertTransform p =
    flatten $ mulX $ fromCoefficients [p' .^ k | k <- [1..]] .* (-1)
  where
    p' = divX p

{- |
'pexp' specialized to sequences of integers.

=== __Examples__

The generating function for the number of ways to partition \(n\)
unlabelled elements (<https://oeis.org/A000041 OEIS A000041>)
is \( PE \left[\frac{x}{1-x}\right] \):

>>> coefficients $ pexpInteger $ mulX recipOneMinus
[1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231,297,385,490,...

Its reciprocal, the Euler function
(`euler`, <https://oeis.org/A010815 OEIS A010815>)
can be obtained by negating the argument of 'pexp':

>>> coefficients $ pexpInteger $ negate $ mulX recipOneMinus
[1,-1,-1,0,0,1,0,1,0,0,0,0,-1,0,0,-1,0,0,0,0,0,0,1,0,0,0,1,0,0,0,...

Since \(n\)-node rooted unlabelled trees are in one-to-one correspondence
with \(n-1\)-node forests of rooted unlabelled trees, we can define
the ordinary generating function for the number of \(n\)-node rooted
unlabelled trees (<https://oeis.org/A000081 OEIS A000081>):

>>> let rootedTrees = mulX (pexpInteger rootedTrees)
>>> coefficients rootedTrees
[0,1,1,2,4,9,20,48,115,286,719,1842,4766,12486,32973,87811,235381,...

Counting unrooted trees (i.e. connected acyclic undirected graphs,
<https://oeis.org/A000055 OEIS A000055>) can be obtained with a formula
due to Otter (cf. Flajolet & Sedgewick, /Analytic Combinatorics/, p. 481):

>>> let trees = 1 + rootedTrees - mapAdditive (`div` 2) (rootedTrees^2 - rootedTrees .^ 2)
>>> coefficients trees
[1,1,1,1,2,3,6,11,23,47,106,235,551,1301,3159,7741,19320,48629,123867,...

(The numbers divided are always even.)

Then the ordinary generating function for the number of acyclic undirected
graphs on \(n\) nodes (<https://oeis.org/A005195 OEIS A005195>) is the
Euler transform of @trees@:

>>> coefficients $ pexpInteger $ trees-1
[1,1,2,3,6,10,20,37,76,153,329,710,1601,3658,8599,20514,49905,122963,...

-}
pexpInteger :: PowerSeries Integer -> PowerSeries Integer
pexpInteger = mapAdditive numerator . pexp . mapAdditive toRational

-- | The inverse of 'pexp'.
plog :: (Eq a, FromRational a) => PowerSeries a -> PowerSeries a
plog b = divN (inverseLambertTransform (mulN (negate logRecipOneMinus `compose` (1-b))))

-- | Multiply the \(n\)th term by \(n\).
mulN :: (Semiring a) => PowerSeries a -> PowerSeries a
mulN p = mulX (derivative p)

-- | Divide the \(n\)th term by \(n\).
divN :: (FromRational a) => PowerSeries a -> PowerSeries a
divN p = integral (divX p)

{- $ogfs

A power series \( \sum_{k=0} a_k x^k \) may be viewed as an ordinary
generating function for the sequence \( \{ a_k \} \).  This sequence
may be extracted using 'coefficients'.

=== Examples

* The generating function of \( \{ {1 \over k} \} \) is \(\log {1 \over 1-x}\):

>>> coefficients logRecipOneMinus
[0 % 1,1 % 1,1 % 2,1 % 3,1 % 4,1 % 5,1 % 6,1 % 7,1 % 8,...

* Multiplying a generating function by \( {1 \over 1-x} \) generates a
sequence of partial sums.
An example is the Harmonic numbers \(H_n = \sum_{k=1}^n {1 \over k}\)
(<https://oeis.org/A001008 OEIS A001008> over
<https://oeis.org/A002805 OEIS A002805>):

>>> coefficients $ recipOneMinus * logRecipOneMinus
[0 % 1,1 % 1,3 % 2,11 % 6,25 % 12,137 % 60,49 % 20,363 % 140,...

* The Mertens function (<https://oeis.org/A002321 OEIS A002321>) consists of
partial sums of the Möbius function:

>>> coefficients $ recipOneMinus * inverseLambertTransform identity
[0,1,0,-1,-1,-2,-1,-2,-2,-2,-1,-2,-2,-3,-2,-1,-1,-2,-2,-3,...

* The Catalan numbers (<https://oeis.org/A000108 OEIS A000108>)
are generated by the solution of the equation \( C = 1 + x C^2 \),
namely the function \( 1 - \sqrt{1-4x} \over 2x \):

>>> let catalan = one + mulX (catalan*catalan)
>>> coefficients catalan
[1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900,2674440,...

* Yet another way to construct the generating function of the Catalan
numbers is to observe that the above equation is equivalent to requiring
that \(C-1\) is a solution to \( x = { y \over {(1+y)}^2 } \), which
can be obtained by inversion:

>>> coefficients $ 1 + inverseSimple (mulX (derivative recipOneMinus .* (-1)))
[1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012,742900,2674440,...

* The derivative of \( 1 - \sqrt{1-4x} \over 2 \)
is \( 1 \over \sqrt{1 - 4x} \), whose coefficients are the
central binomial coefficients \( \binom{2n}{n} = {(2n!) \over {n!}^2} \)
(<https://oeis.org/A000984 OEIS A000984>):

>>> coefficients $ derivative $ mulX catalan
[1,2,6,20,70,252,924,3432,12870,48620,184756,705432,2704156,...

* The number of ways to partition \(n\) unlabelled elements
(<https://oeis.org/A000041 OEIS A000041>) is generated by the reciprocal
of 'euler'.
(This is the number of terms in the \(n\)th Bell polynomial:
see "Data.YAP.PowerSeries.Maclaurin#g:Bell_polynomials".)

>>> coefficients $ recipSimple euler
[1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231,297,385,490,...

* The number of ways to partition \(n\) unlabelled elements into parts
of distinct sizes or equivalently the number of partitions into odd parts
(<https://oeis.org/A000009 OEIS A000009>) is generated by

\[
    \prod_{k=1}^{\infty} \frac{1}{1 - x^{2k-1}}
    =
    {
    \prod_{k=1}^{\infty} 1 - x^{2k}
    \over
    \prod_{k=1}^{\infty} 1 - x^k
    }
\]

>>> coefficients $ euler .^ 2 * recipSimple euler
[1,1,1,2,2,3,4,5,6,8,10,12,15,18,22,27,32,38,46,54,64,76,89,104,...

* The Ramanujan tau function (<https://oeis.org/A000594 OEIS A000594>):

>>> coefficients $ mulX (euler^24)
[0,1,-24,252,-1472,4830,-6048,-16744,84480,-113643,-115920,534612,...

* The ratios of successive terms of Stern's diatomic series
  (<https://oeis.org/A002487 OEIS A002487>) define an enumeration of
  the non-negative rationals.  The generating function of the sequence
  satisfies \(x A(x) = (1 + x + x^2)A(x^2)\), which, with a little
  manipulation, yields

>>> let sternAux = 1 + mulX (1 + fromCoefficients [1,1,1]*sternAux .^ 2)
>>> coefficients $ mulX (1 + mulX sternAux)
[0,1,1,2,1,3,2,3,1,4,3,5,2,5,3,4,1,5,4,7,3,8,5,7,2,7,5,8,3,7,4,5,...

-}

{- |
@'linearRecurrence' a b@, where @a@ and @b@ are lists of length \(k\),
yields an ordinary generating function for the sequence \( \{c_n\} \)
defined by the recurrence

\[
    \begin{align}
        c_0 & = b_0 \\
        & \vdots \\
        c_{k-1} & = b_{k-1} \\
        c_{n+k} & = a_0 c_{n+k-1} + \cdots + a_{k-1} c_n
    \end{align}
\]

The generating function for this sequence is

\[ c(z) = {b(z) (1 - z a(z)) \mod z^k \over 1 - z a(z)} \]

=== __Examples__

* Fibonacci numbers (<https://oeis.org/A000045 OEIS A000045>):

\[
    \begin{align}
        F_0 & = 0 \\
        F_1 & = 1 \\
        F_{n+2} & = F_{n+1} + F_n
    \end{align}
\]

>>> coefficients $ linearRecurrence [1,1] [0,1]
[0,1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,...

* Lucas numbers (<https://oeis.org/A000032 OEIS A000032>):

\[
    \begin{align}
        L_0 & = 2 \\
        L_1 & = 1 \\
        L_{n+2} & = L_{n+1} + L_n
    \end{align}
\]

>>> coefficients $ linearRecurrence [1,1] [2,1]
[2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207,3571,5778,...

* Pell numbers (<https://oeis.org/A000129 OEIS A000129>):

\[
    \begin{align}
        P_0 & = 0 \\
        P_1 & = 1 \\
        P_{n+2} & = 2 P_{n+1} + P_n
    \end{align}
\]

>>> coefficients $ linearRecurrence [2,1] [0,1]
[0,1,2,5,12,29,70,169,408,985,2378,5741,13860,33461,80782,195025,...

* Pell-Lucas numbers (<https://oeis.org/A002203 OEIS A002203>):

\[
    \begin{align}
        Q_0 & = Q_1 = 2 \\
        Q_{n+2} & = 2 Q_{n+1} + Q_n
    \end{align}
\]

>>> coefficients $ linearRecurrence [2,1] [2,2]
[2,2,6,14,34,82,198,478,1154,2786,6726,16238,39202,94642,228486,...

* Padovan sequence (<https://oeis.org/A000931 OEIS A000931>):

\[
    \begin{align}
        P_0 & = P_1 = P_2 = 1 \\
        P_{n+3} & = P_{n+1} + P_n
    \end{align}
\]

>>> coefficients $ linearRecurrence [0,1,1] [1,1,1]
[1,1,1,2,2,3,4,5,7,9,12,16,21,28,37,49,65,86,114,151,...

* Perrin sequence (<https://oeis.org/A001608 OEIS A001608>):

\[
    \begin{align}
        P_0 & = 3 \\
        P_1 & = 0 \\
        P_2 & = 2 \\
        P_{n+3} & = P_{n+1} + P_n
    \end{align}
\]

>>> coefficients $ linearRecurrence [0,1,1] [3,0,2]
[3,0,2,3,2,5,5,7,10,12,17,22,29,39,51,68,90,119,158,209,...

-}
linearRecurrence :: (Ring a) => [a] -> [a] -> PowerSeries a
linearRecurrence recurrence initial = divOneMinus r q
  where
    k = max (length recurrence) (length initial)
    p = fromCoefficients initial
    q = fromCoefficients recurrence
    r = fromCoefficients (take k (coefficients (p*(1 - identity*q))))

{- |
Infinite formal languages: the \(n\)th element of the sequence is
a finite set of strings of length \(n\).

=== __Examples__

* Addition is union of languages:

>>> coefficients $ string "ab" + string "c"
[fromList [],
 fromList ["c"],
 fromList ["ab"],
 fromList [],
 fromList [],...

* Multiplication is concatenation:

>>> coefficients $ (string "ab" + string "c") * (string "d" + string "ef")
[fromList [],
 fromList [],
 fromList ["cd"],
 fromList ["abd","cef"],
 fromList ["abef"],
 fromList [],...

* Kleene star is a sum of powers:

>>> let star l = recipOneMinus `compose` mulX (divX l)
>>> coefficients $ star $ string "ab" + string "c"
[fromList [""],
 fromList ["c"],
 fromList ["ab","cc"],
 fromList ["abc","cab","ccc"],
 fromList ["abab","abcc","cabc","ccab","cccc"],...

-}
type GradedLanguage a = PowerSeries (FiniteLanguage a)

-- | A language consisting of a single string.
string :: (Ord a) => [a] -> GradedLanguage a
string s = fromCoefficients (replicate (length s) zero ++ [singleton s])

{- $pgf
A power series whose coefficients sum to 1 may encode the probabilites of
each possible value of a natural number-valued random variable \(X\),
i.e. \( p_k = \Pr(X = k) \).
Such a series is then the probability generating function \(E[z^X]\).

* `one` is the PGF for the constant random variable with value 0.

* `identity` is the PGF for the constant random variable with value 1.

* If @pX@ is the PGF for the random variable \(X\), then the PGF for
  \(c X\) for natural number \(c\) is @pX .^ c@.

* The product of PGFs for independent random variables \(X\) and \(Y\)
  is the PGF for \(X+Y\).

* The sum of the coefficients of the derivative of a PGF is the expected
  value of the random variable.
-}

-- | The distribution of a single Bernoulli trial with probability \(p\)
-- of success has generating function \((1-p) + p z\).
--
-- Powers of this distribution yield the binomial distribution.
bernoulliPGF :: (Ring a) => a -> PowerSeries a
bernoulliPGF p = fromCoefficients [1-p, p]

-- | The geometric distribution, of the number of Bernoulli trials with
-- probability \(p\) before the first success,
-- has generating function \( {p \over 1 - (1-p)z} \).
--
-- Powers of this distribution yield the negative binomial or Pascal
-- distribution.
geometricPGF :: (Ring a) => a -> PowerSeries a
geometricPGF p = constant p * (recipOneMinus .* (1-p))

-- | The Poisson distribution with parameter \(\lambda\), of the number
-- of events with mean rate \(\lambda\) occurring in an interval,
-- has generating function \( e^{\lambda(z-1)} \).
poissonPGF :: (Floating a) => a -> PowerSeries a
poissonPGF l = constant (exp l) * expS .* l

{- $polynomial_sequences
A polynomial sequence is a sequence of polynomials \(\{p_n(x)\}\)
where each polynomial \(p_n\) has degree at most \(n\), so that
the coefficients form a triangle.  Such sequences can be defined
by ordinary generating functions of the form

\[
\sum_{n=0}^\infty p_n(x) t^n
\]

=== Examples

For convenience, define

>>> import qualified Data.YAP.Polynomial as Poly
>>> let x = Poly.identity

The sequence of polynomials with binomial coefficients
(Pascal's triangle, <https://oeis.org/A007318 OEIS A007318>)
has the generating
function \( {1 \over 1 - (1+x)t} = \sum_{n=0}^\infty {(1+x)}^n t^n \):

>>> coefficients $ compose recipOneMinus $ mulX $ constant $ 1 + x
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,2,1],
 fromCoefficients [1,3,3,1],
 fromCoefficients [1,4,6,4,1],
 fromCoefficients [1,5,10,10,5,1],...

Chebyshev polynomials of the first kind
(<https://oeis.org/A053120 OEIS A053120>)
satisfy \( \cos (n \theta) = T_n(\cos \theta) \).
They are defined by the linear recurrence

\[
    \begin{align}
        T_0(x) & = 1 \\
        T_1(x) & = x \\
        T_{n+2}(x) & = 2 x\,T_{n+1}(x) - T_n(x)
    \end{align}
\]

or equivalently by the generating function \(1 - xt \over 1 - 2xt + t^2\).

>>> coefficients $ linearRecurrence [2*x, -1] [1, x]
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [-1,0,2],
 fromCoefficients [0,-3,0,4],
 fromCoefficients [1,0,-8,0,8],
 fromCoefficients [0,5,0,-20,0,16],...

Chebyshev polynomials of the second kind
(<https://oeis.org/A053117 OEIS A053117>)
satisfy \( \sin\big((n + 1)\theta\big) = U_n(\cos \theta) \sin \theta \).
They are defined by the linear recurrence

\[
    \begin{align}
        U_0(x) & = 1 \\
        U_1(x) & = 2 x \\
        U_{n+2}(x) & = 2 x\,U_{n+1}(x) - U_n(x)
    \end{align}
\]

or equivalently by the generating function \(1 \over 1 - 2xt + t^2\).

>>> coefficients $ linearRecurrence [2*x, -1] [1, 2*x]
[fromCoefficients [1],
 fromCoefficients [0,2],
 fromCoefficients [-1,0,4],
 fromCoefficients [0,-4,0,8],
 fromCoefficients [1,0,-12,0,16],
 fromCoefficients [0,6,0,-32,0,32],...

The sequence of Legendre polynomials
(numerators <https://oeis.org/A100258 OEIS A100258>)
has the generating function \( 1 \over \sqrt{1 - 2xt + t^2} \):

>>> coefficients $ powerOnePlus (-0.5) `compose` fromCoefficients [0, -2*x, 1]
[fromCoefficients [1 % 1],
 fromCoefficients [0 % 1,1 % 1],
 fromCoefficients [(-1) % 2,0 % 1,3 % 2],
 fromCoefficients [0 % 1,(-3) % 2,0 % 1,5 % 2],
 fromCoefficients [3 % 8,0 % 1,(-15) % 4,0 % 1,35 % 8],
 fromCoefficients [0 % 1,15 % 8,0 % 1,(-35) % 4,0 % 1,63 % 8],...

The Catalan or Narayana triangle (<https://oeis.org/A090181 OEIS A090181>)
has a generating function \(A(x,t)\)
satisfying \(A(x,t) = 1 + {x t A(x,t) \over 1 - t A(x,t)}\):

>>> narayama = 1 + constant Poly.identity * (mulX recipOneMinus `compose` mulX narayama)
>>> coefficients narayama
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,1,3,1],
 fromCoefficients [0,1,6,6,1],
 fromCoefficients [0,1,10,20,10,1],...

Row sums (i.e. \(x = 1\)) are Catalan numbers
(<https://oeis.org/A000108 OEIS A000108>).

The triangle of partition numbers (<https://oeis.org/A008284 OEIS A008284>)
has generating function

\[
	\exp\left( \sum_{n=1}^\infty \frac{x^n}{n} \frac{t^n}{1-t^n} \right) - 1
	= \sum_{n=0}^\infty \left( \sum_{k=0}^\infty T(n, k) x^k \right) t^n
\]

where \( T(n, k) \) is the number of partitions of \(n\) in which the
greatest is \(k\), and equivalently the number of partitions of \(n\)
into \(k\) positive parts:

>>> map (mapAdditive Data.Ratio.numerator) $ coefficients $ compose expS (lambertTransform (integral (divX monomials))) - 1
[fromCoefficients [],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,1,1,1],
 fromCoefficients [0,1,2,1,1],
 fromCoefficients [0,1,2,2,1,1],
 fromCoefficients [0,1,3,3,2,1,1],...

Row sums (i.e. \(x = 1\)) are the number of ways to partition \(n\)
unlabelled elements (<https://oeis.org/A000041 OEIS A000041>).

-}

-- | Promotion of a power series to a power series of constant polynomials
constants :: (AdditiveMonoid a) => PowerSeries a -> PowerSeries (Polynomial a)
constants f = mapAdditive Poly.constant f

-- | \(1 \over 1 - xt\), the generating function for the sequence of
-- monomials \(\{x^n\}\)
monomials :: (Eq a, Semiring a) => PowerSeries (Polynomial a)
monomials = recipOneMinusOf (constant Poly.identity)

{- | The Riordan array generated by series \(f\) and \(g\), with \(g(0) = 0\),
is a polynomial sequence with ordinary generating function

\[
    {f(t) \over 1 - x g(t)} =
        f(t) \left( 1 + x g(t) + (x g(t))^2 + \cdots \right)
\]

which can be constructed as
@`constants` f * `compose` `monomials` (`constants` g)@.

Setting \(x = 1\) yields \( {f(t) \over 1 - g(t)} \), the ordinary
generating function of the sequence of sums of the coefficients of
the rows.

Since \(g(t)\) is required have a constant term of zero, and thus
has the form \(g(t) = x h(t)\), some authors use the equivalent definition

\[
    {f(t) \over 1 - x t h(t)} =
        f(t) \left( 1 + x t h(t) + (x t h(t))^2 + \cdots \right)
\]

=== __Examples__

* The sequence of polynomials with binomial coefficients
(Pascal's triangle, <https://oeis.org/A007318 OEIS A007318>):

>>> coefficients $ riordan recipOneMinus (mulX recipOneMinus)
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,2,1],
 fromCoefficients [1,3,3,1],
 fromCoefficients [1,4,6,4,1],
 fromCoefficients [1,5,10,10,5,1],...

* The Catalan triangle (<https://oeis.org/A033184 OEIS A033184>):

>>> coefficients $ riordan catalan (mulX catalan)
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [2,2,1],
 fromCoefficients [5,5,3,1],
 fromCoefficients [14,14,9,4,1],
 fromCoefficients [42,42,28,14,5,1],...

-}
riordan :: (Semiring a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries (Polynomial a)
riordan f g =
    mapAdditive Poly.constant f `divOneMinus` mapAdditive Poly.linear (divX g)

-- This is the form used by
-- * Luschny, discarding constant term of g(t)
-- * Riordan Group book, requiring constant term of g(t) is zero
--
-- Sprugnoli uses f(t) \over 1 - t x g(t), so defined for any series,
-- and corresponding to the Bell transform rather than a Sheffer sequence.

{- | Deléham's delta operator (<https://oeis.org/A084938 OEIS A084938>)
takes two sequences \(\{r_n\}\) and \(\{s_n\}\) and forms the Stieltjes
fraction defined by the sequence of polynomials \(\{r_n + s_n x\}\),
yielding the ordinary generating function of a polynomial sequence.

=== __Examples__

* Another definition of the Catalan or Narayana triangle
(<https://oeis.org/A090181 OEIS A090181>):

>>> coefficients $ delta (cycle [0, 1]) (cycle [1, 0])
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,1,3,1],
 fromCoefficients [0,1,6,6,1],
 fromCoefficients [0,1,10,20,10,1],...

* The sequence of rising factorial polynomials with coefficients the
unsigned Stirling numbers of the first kind
(<https://oeis.org/A132393 OEIS A132393>), the number of permutations
of \(n\) elements that have exactly \(k\) cycles.

>>> coefficients $ delta (0:concat [[n, n] | n <- [1..]]) (cycle [1, 0])
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,2,3,1],
 fromCoefficients [0,6,11,6,1],
 fromCoefficients [0,24,50,35,10,1],...

* The sequence of Touchard polynomials with coefficients the Stirling
numbers of the second kind (<https://oeis.org/A048993 OEIS A048993>),
the number of ways to partition a set of \(n\) elements into \(k\)
non-empty subsets:

>>> coefficients $ delta (concat [[0, n] | n <- [1..]]) (cycle [1, 0])
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,1,3,1],
 fromCoefficients [0,1,7,6,1],
 fromCoefficients [0,1,15,25,10,1],...

* The sequence of Eulerian polynomials with coefficients the Eulerian
numbers \(A(n,k)\) (<https://oeis.org/A123125 OEIS A123125>), the number
of permutations of the numbers 1 to \(n\) in which exactly \(k\) elements
are greater than the previous element.

>>> coefficients $ delta (concat [[n, 0] | n <- [1..]]) (concat [[0, n] | n <- [1..]])
[fromCoefficients [1],
 fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,4,1],
 fromCoefficients [1,11,11,1],
 fromCoefficients [1,26,66,26,1],...

-}
delta :: (Semiring a) => [a] -> [a] -> PowerSeries (Polynomial a)
delta r s =
    stieltjes (longZipWith (+) (map Poly.constant r) (map Poly.linear s))

-- A085880 = delta (repeat one) (repeat one)

{- $necklace_polynomials

The polynomials \(n M_n(x)\) of the Möbius triangle
(<https://oeis.org/A363914 OEIS A363914>) satisfy
 
\[ x^n = \sum_{d \mid n} d M_d(x) \]
 
so they can be obtained from the series of monomials by Möbius inversion:
 
>>> coefficients $ inverseLambertTransform monomials
[fromCoefficients [],
 fromCoefficients [0,1],
 fromCoefficients [0,-1,1],
 fromCoefficients [0,-1,0,1],
 fromCoefficients [0,0,-1,0,1],
 fromCoefficients [0,-1,0,0,0,1],
 fromCoefficients [0,1,-1,-1,0,0,1],
 fromCoefficients [0,-1,0,0,0,0,0,1],
 fromCoefficients [0,0,0,0,-1,0,0,0,1],...

\(n M_n(k)\) gives the number of aperiodic strings of length \(n\) drawn
from \(k\) letters (<https://oeis.org/A143324 OEIS A143324>).
Hence \(M_n(k)\) is the number of aperiodic necklaces on \(n\) beads
with at most \(k\) colours (<https://oeis.org/A074650 OEIS A074650>)
and the necklace polynomials \(M_n(x)\) are generated by:

>>> necklace = integral $ divX $ inverseLambertTransform monomials
>>> coefficients necklace
[fromCoefficients [],
 fromCoefficients [0 % 1,1 % 1],
 fromCoefficients [0 % 1,(-1) % 2,1 % 2],
 fromCoefficients [0 % 1,(-1) % 3,0 % 1,1 % 3],
 fromCoefficients [0 % 1,0 % 1,(-1) % 4,0 % 1,1 % 4],
 fromCoefficients [0 % 1,(-1) % 5,0 % 1,0 % 1,0 % 1,1 % 5],
 fromCoefficients [0 % 1,1 % 6,(-1) % 6,(-1) % 6,0 % 1,0 % 1,1 % 6],...

Then the general necklace polynomials yielding the number of necklaces on \(n\)
beads with at most \(k\) colours (<https://oeis.org/A075195 OEIS A075195>)
are defined by
 
\[
N_n(k) = \sum_{d \mid n} M_d(k)
\]
 
and the sequence \(N_n(x)\)
(<https://oeis.org/A054523 OEIS A054523>) is thus generated by:

>>> generalNecklace = lambertTransform necklace
>>> coefficients generalNecklace
[fromCoefficients [],
 fromCoefficients [0 % 1,1 % 1],
 fromCoefficients [0 % 1,1 % 2,1 % 2],
 fromCoefficients [0 % 1,2 % 3,0 % 1,1 % 3],
 fromCoefficients [0 % 1,1 % 2,1 % 4,0 % 1,1 % 4],
 fromCoefficients [0 % 1,4 % 5,0 % 1,0 % 1,0 % 1,1 % 5],
 fromCoefficients [0 % 1,1 % 3,1 % 3,1 % 6,0 % 1,0 % 1,1 % 6],...

-}

{- |
The two-variable version of the Lambert transform maps
a power series \( A(x,t) \) (with a zero constant term) to:

\[
	B(x, t) = \sum_{n=1}^\infty A(x^n, t^n)
\]

The coefficients of the two polynomial series are related by

\[ b_{n,k} = \sum_{m \mid n, j \mid k} a_{m,j} \]

-}
lambertTransform2 :: (AdditiveMonoid a) =>
    PowerSeries (Polynomial a) -> PowerSeries (Polynomial a)
lambertTransform2 p =
    flatten $ mulX $ fromCoefficients
        [mapAdditive (Poly..^ k) p' .^ k | k <- [1..]]
  where
    p' = divX p

{- |
The inverse of 'lambertTransform2' computes the Möbius transform of the
generated sequence, and can be computed from

\[
	A(x, t) = B(x, t) - \sum_{n=2}^\infty A(x^n, t^n)
\]

provided \(B(x,t)\) has a zero constant term.

-}
inverseLambertTransform2 :: Ring a =>
    PowerSeries (Polynomial a) -> PowerSeries (Polynomial a)
inverseLambertTransform2 q = mulX p'
  where
    p' = divX q - flatten (fromCoefficients
        (0 : [mapAdditive (Poly..^ k) p' .^ k | k <- [2..]]))

{- |
The two-variable form of the plethystic exponential (or Euler transform)
of a series \(A(x,t)\) with \(a_0 = 0\) is

\[
	PE[A](x,t)
	= \exp \left( \sum_{n=1}^\infty {A(x^n, t^n) \over n} \right)
\]

The transformation has a combinatorial interpretation.
If \(a_{n,k}\) is the number of objects of some kind having weights \(n\)
and \(k\), then \(PE[A]\) generates the sequence whose element at
position \(n,k\) is the number of multisets of these objects having total
weights \(n\) and \(k\).  For example, if \(a_{n,k}\) is the number
of connected graphs with \(n\) nodes and \(k\) edges, then \(PE[A]\)
generates the sequence whose element at position \(n,k\) is the number
of graphs with \(n\) nodes and \(k\) edges.

-}
pexp2 :: (Eq a, FromRational a) =>
    PowerSeries (Polynomial a) -> PowerSeries (Polynomial a)
pexp2 a = expS `compose` divN (lambertTransform2 (mulN a))

-- | The inverse of 'pexp2'.
plog2 :: (Eq a, FromRational a) =>
    PowerSeries (Polynomial a) -> PowerSeries (Polynomial a)
plog2 b =
    divN $ inverseLambertTransform2 $ mulN $
        negate logRecipOneMinus `compose` (1-b)

-- Multivariate polynomial sequences

-- | The ordinary generating function \( \sum_{n=1}^\infty x_n t^n \),
-- the multinomial counterpart of \(xt \over 1-t\).
ordXs :: (Eq a, Semiring a) => PowerSeries (MultiPolynomial Xs a)
ordXs = fromCoefficients (zero:allXs)

-- | The logarithmic generating function \( \sum_{n=1}^\infty x_n \frac{t^n}{n} \),
-- the multinomial counterpart of \(x \log \frac{1}{1-t}\).
logXs :: (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
logXs = integral (fromCoefficients allXs)

-- Cycle index polynomials

-- | The cycle index polynomials for identity groups \(E_n\) are
-- generated by \( 1 \over 1 - x_1 t \).
identityCycleIndices ::
    (Eq a, Semiring a) => PowerSeries (MultiPolynomial Xs a)
identityCycleIndices = compose recipOneMinus $ fromCoefficients [zero, x1]
  where
    x1:_ = allXs

-- | The cycle index polynomials for the permutation groups on \(n\)
-- elements consisting of the identity and reversal permutation are
-- generated by \( 1 + x_1 t \over 1 - x_2 t^2 \).
reversalCycleIndices ::
    (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
reversalCycleIndices =
    0.5*(identityCycleIndices + (one + x1t) * compose recipOneMinus x2t2)
  where
    x1:x2:_ = allXs
    -- x_1 t
    x1t = fromCoefficients [zero, x1]
    -- x_2 t^2
    x2t2 = fromCoefficients [zero, zero, x2]

-- | The cycle index polynomials for cyclic groups \(C_n\)
-- (<https://oeis.org/A212357 OEIS A212357>) are generated by
--
-- \[ 1 - \sum_{k \geq 1} \frac{\phi(k)}{k} \log(1 - x_k t^k) \]
cyclicCycleIndices ::
    (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
cyclicCycleIndices =
    one +
    (sumPowers $
        zipWith3 term (tail (coefficients totient)) [(1::Int)..] allXs)
  where
    term phi k xk =
        fromRational (toRational phi / toRational k) *
        compose logRecipOneMinus (mulX (constant xk))

-- Euler's totient function (phi, A000010)
totient :: PowerSeries Int
totient = inverseLambertTransform $ mulX $ derivative recipOneMinus

-- sum (zipWith (.^) ps [1..])
-- each power series must have zero constant term
sumPowers :: (Eq a, AdditiveMonoid a) => [PowerSeries a] -> PowerSeries a
sumPowers ps =
    flatten (fromCoefficients (zero:[divX p .^ k | (p, k) <- zip ps [1..]]))

{- |
The cycle index polynomials for dihedral groups \(D_n\)
(<https://oeis.org/A212355 OEIS A212355>) are generated by:

\[
\sum_{n=1}^\infty Z(D_n)(\bar x) t^n =
	\frac{1}{2} \sum_{n=1}^\infty Z(C_n)(\bar x) t^n +
	\frac{2 x_1 t + x_1^2 t^2 + x_2 t^2}{4(1 -  x_2 t^2)}
\]

-}
dihedralCycleIndices ::
    (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
dihedralCycleIndices = 0.5*cyclicCycleIndices + dihedralExtra

dihedralExtra ::
    (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
dihedralExtra =
    (0.5*x1t + 0.25*(x1t*x1t + x2t2)) * compose recipOneMinus x2t2
  where
    x1:x2:_ = allXs
    -- x_1 t
    x1t = fromCoefficients [zero, x1]
    -- x_2 t^2
    x2t2 = fromCoefficients [zero, zero, x2]

{- |
The cycle index polynomials for symmetric groups \( S_n \)
(<https://oeis.org/A036039 OEIS A036039> or
<https://oeis.org/A279038 OEIS A279038>) are generated by:

\[
\sum_{n=1}^\infty Z(S_n)(\bar x) t^n
	= \exp \left( \sum_{n=1}^\infty \frac{x_n}{n} t^n \right) - 1
\]

=== __Examples__

>>> import Data.YAP.FiniteMap
>>> map pretty $ coefficients symmetricCycleIndices
["1 % 1",
 "x1",
 "(1 % 2)*x2 + (1 % 2)*x1^2",
 "(1 % 3)*x3 + (1 % 2)*x1*x2 + (1 % 6)*x1^3",
 "(1 % 4)*x4 + (1 % 3)*x1*x3 + (1 % 8)*x2^2 + (1 % 4)*x1^2*x2 + (1 % 24)*x1^4",...

For example, the 4th entry encodes the polynomial

\[
Z(S_4) = \frac{1}{24} (6 x_4 + 8 x_1 x_3 + 3 x_2^2 + 6 x_1^2 x_2 + x_1^4)
\]

Indeed each polynomial \(Z(S_n)\) is a polynomial with integer
coefficients divided by \(n!\).

-}
symmetricCycleIndices ::
    (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
symmetricCycleIndices = compose expS logXs

{- |
The cycle index polynomials for alternating groups \(A_n\)
(<https://oeis.org/A212358 OEIS A212358>) are generated by:

\[
\sum_{n=1}^\infty Z(A_n)(\bar x) t^n =
	\sum_{n=1}^\infty Z(S_n)(\bar x) t^n +
	\exp \left( - \sum_{n=1}^\infty \frac{x_n}{n} (-t)^n \right) - 1 - x_1
\]

-}
alternatingCycleIndices ::
    (Eq a, FromRational a) => PowerSeries (MultiPolynomial Xs a)
alternatingCycleIndices =
    (compose expS $ logXs) +
    (compose expS $ negate $ (logXs .* (-1))) -
    fromCoefficients [one, x1]
  where
    x1:_ = allXs

{- |
Given a cycle index polynomial for a group of permutations of
\(n\) elements, construct the cycle index polynomial for the induced
group of permutations over \(n(n-1) \over 2\) unordered pairs of
elements.  (Harary & Palmer /Graphical Enumeration/, pp. 84-87)

=== __Example__

>>> edgeCycleIndices = mapAdditive pairCycleIndex symmetricCycleIndices
>>> map pretty $ coefficients $ edgeCycleIndices
["1 % 1",
 "1 % 1",
 "x1",
 "(1 % 3)*x3 + (1 % 2)*x1*x2 + (1 % 6)*x1^3",
 "(1 % 4)*x2*x4 + (1 % 3)*x3^2 + (3 % 8)*x1^2*x2^2 + (1 % 24)*x1^6",...

-}
pairCycleIndex :: (Eq a, Semiring a) =>
    MultiPolynomial Xs a -> MultiPolynomial Xs a
pairCycleIndex = mapIndices (fmap pairCycles)

type Partition = Multiset Xs

{- |
Convert a partition of \(n\) representing cyclic decompositions of
permutations of n elements into a partition of \(n(n-1) \over 2\) representing
cyclic decompositions of permutations of pairs of elements.
-}
pairCycles :: Partition -> Partition
pairCycles p = sum (map sameCycle ts) + diffCycle ts
  where
    ts = assocs p

diffCycle :: [(Xs, Natural)] -> Partition
diffCycle ts =
    sum (map sameLengthDiffCycle ts) +
    sum [diffLength t1 t2 | t1:rest <- tails ts, t2 <- rest]

-- cycles of pairs within the same cycle
sameCycle :: (Xs, Natural) -> Partition
sameCycle (X k, j) = atimes j (pairCycle k)

-- cycles of pairs within a cycle of length k >= 1
pairCycle :: Natural -> Partition
pairCycle k
  | odd k = fromAssocs [(X k, k `div` two)]
  | otherwise =
    fromAssocs [(X (k `div` two), one), (X k, predNat (k `div` two))]

-- cycles of pairs between different cycles of the same length
sameLengthDiffCycle :: (Xs, Natural) -> Partition
sameLengthDiffCycle (X k, j) =
    fromAssocs [(X k, k * j * predNat j `div` two)]

-- cycles of pairs between cycles of different lengths
diffLength :: (Xs, Natural) -> (Xs, Natural) -> Partition
diffLength (X k1, j1) (X k2, j2) =
    fromAssocs [(X (lcm k1 k2), gcd k1 k2*j1*j2)]

two :: Natural
two = one + one

predNat :: Natural -> Natural
predNat n = maybe zero id (minusNaturalMaybe n one)

{- |
Given a cycle index polynomial for a group of permutations of \(n\) elements,
construct the cycle index polynomial for the induced group of permutations
over \(n(n-1)\) ordered pairs of distinct elements.  (Harary & Palmer
/Graphical Enumeration/, pp. 121-122)

=== __Example__

>>> directedEdgeCycleIndices = mapAdditive orderedPairCycleIndex symmetricCycleIndices
>>> map pretty $ coefficients $ directedEdgeCycleIndices
["1 % 1",
 "1 % 1",
 "(1 % 2)*x2 + (1 % 2)*x1^2",
 "(1 % 3)*x3^2 + (1 % 2)*x2^3 + (1 % 6)*x1^6",
 "(1 % 4)*x4^3 + (1 % 3)*x3^4 + (1 % 8)*x2^6 + (1 % 4)*x1^2*x2^5 + (1 % 24)*x1^12",...

-}
orderedPairCycleIndex :: (Eq a, Semiring a) =>
    MultiPolynomial Xs a -> MultiPolynomial Xs a
orderedPairCycleIndex = mapIndices (fmap ordPairCycles)

-- Convert a partition of n representing cyclic decompositions of
-- permutations of \(n\) elements into a partition of \(n(n-1)\)
-- representing cyclic decompositions of permutations of ordered pairs
-- of distinct elements.
ordPairCycles :: Partition -> Partition
ordPairCycles p =
    sum (map ordSameCycle ts) + atimes (2::Int) (diffCycle ts)
  where
    ts = assocs p

-- cycles of ordered pairs within the same cycle
ordSameCycle :: (Xs, Natural) -> Partition
ordSameCycle (X k, j) = fromAssocs [(X k, predNat k * j)]

-- | Pólya enumeration formula, mapping a multivariate polynomial
-- \( P(x_1, \ldots, x_n) \) to \( P(A(x), \ldots, A(x^n)) \).
-- Typically
--
-- * \(P\) is the cycle index of a permutation group \(G\) over a
--   finite set \(X\), and
--
-- * \(A\) is the ordinary generating function of the
-- number of elements of a set \(Y\) of each size.
--
-- Then the result is the ordinary generating function of the number
-- of \(G\)-equivalence classes of functions from \(X\) to \(Y\) of
-- each total size.
polyaEnumeration :: (Eq a, Semiring a) =>
    MultiPolynomial Xs a -> Polynomial a -> Polynomial a
polyaEnumeration z p = evaluate subs Poly.constant z
  where
    subs (X k) = p Poly..^ fromIntegral k

{- |
Given the cycle index multivariate polynomial of a permutation
group \(G\) over a finite set \(X\), returns a polynomial whose \(k\)th
coefficient is the number of \(G\)-equivalence classes of \(k\)-sets
of \(X\).
This is the special case of `polyaEnumeration` with polynomial \(1+x\).

=== __Examples__

Each dihedral group \(D_n\) describes symmetries of bracelets (cycles that
can be turned over) of \(n\) beads.  Hence the number of such bracelets
with \(k\) black beads and \(n-k\) white beads
(<https://oeis.org/A052307 OEIS A052307>) is enumerated by

>>> bracelets = mapAdditive equivalenceClasses dihedralCycleIndices
>>> map (mapAdditive Data.Ratio.numerator) $ coefficients bracelets
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,1,1],
 fromCoefficients [1,1,1,1],
 fromCoefficients [1,1,2,1,1],
 fromCoefficients [1,1,2,2,1,1],
 fromCoefficients [1,1,3,3,3,1,1],
 fromCoefficients [1,1,3,4,4,3,1,1],
 fromCoefficients [1,1,4,5,8,5,4,1,1],...

An enumeration of unlabelled undirected graphs with \(n\) nodes
and \(k\) edges (<https://oeis.org/A008406 OEIS A008406>):

>>> edgeCycleIndices = mapAdditive pairCycleIndex symmetricCycleIndices
>>> numGraphs = mapAdditive equivalenceClasses edgeCycleIndices
>>> map (mapAdditive Data.Ratio.numerator) $ coefficients numGraphs
[fromCoefficients [1],
 fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,1,1,1],
 fromCoefficients [1,1,2,3,2,1,1],
 fromCoefficients [1,1,2,4,6,6,6,4,2,1,1],
 fromCoefficients [1,1,2,5,9,15,21,24,24,21,15,9,5,2,1,1],...

An enumeration of connected unlabelled undirected graphs with \(n\) nodes
and \(k\) edges (<https://oeis.org/A054924 OEIS A054924>):

>>> map (mapAdditive Data.Ratio.numerator) $ coefficients $ plog2 numGraphs
[fromCoefficients [],
 fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,0,1,1],
 fromCoefficients [0,0,0,2,2,1,1],
 fromCoefficients [0,0,0,0,3,5,5,4,2,1,1],
 fromCoefficients [0,0,0,0,0,6,13,19,22,20,14,9,5,2,1,1],...

An enumeration of unlabelled directed graphs with \(n\) nodes
and \(k\) edges (<https://oeis.org/A052283 OEIS A052283>):

>>> directedEdgeCycleIndices = mapAdditive orderedPairCycleIndex symmetricCycleIndices
>>> numDigraphs = mapAdditive equivalenceClasses directedEdgeCycleIndices
>>> map (mapAdditive Data.Ratio.numerator) $ coefficients numDigraphs
[fromCoefficients [1],
 fromCoefficients [1],
 fromCoefficients [1,1,1],
 fromCoefficients [1,1,4,4,4,1,1],
 fromCoefficients [1,1,5,13,27,38,48,38,27,13,5,1,1],...

An enumeration of weakly connected unlabelled directed graphs with \(n\) nodes
and \(k\) edges (<https://oeis.org/A283753 OEIS A283753>):

>>> map (mapAdditive Data.Ratio.numerator) $ coefficients $ plog2 numDigraphs
[fromCoefficients [],
 fromCoefficients [1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,0,3,4,4,1,1],
 fromCoefficients [0,0,0,8,22,37,47,38,27,13,5,1,1],...

-}
equivalenceClasses ::
    (Eq a, Semiring a) => MultiPolynomial Xs a -> Polynomial a
equivalenceClasses z = polyaEnumeration z (one + Poly.identity)

{- $symmetric_polynomials

The cycle index polynomials express complete homogeneous symmetric polynomials
in terms of power sums \(p_k(x_1,\ldots,x_n)= \sum_{i=1}^n x_i^k\).
The elementary symmetric polynomials are expressed in terms of power sums
by the signed version: (<https://oeis.org/A324254 OEIS A324254>):

>>> map pretty $ coefficients $ compose expS $ negate $ logXs .* (-1)
["1 % 1",
 "x1",
 "((-1) % 2)*x2 + (1 % 2)*x1^2",
 "(1 % 3)*x3 + ((-1) % 2)*x1*x2 + (1 % 6)*x1^3",
 "((-1) % 4)*x4 + (1 % 3)*x1*x3 + (1 % 8)*x2^2 + ((-1) % 4)*x1^2*x2 + (1 % 24)*x1^4",...

The inverse function

\[
\frac{d}{dt} \log \left( 1 + \sum_{n=1}^\infty x_n (-t)^n \right) =
	{\frac{d}{dt} \sum_{n=1}^\infty x_n (-t)^n \over
		1 + \sum_{n=1}^\infty x_n (-t)^n} =
	{ - \sum_{n=1}^\infty n x_n (-t)^{n-1} \over
		1 + \sum_{n=1}^\infty x_n (-t)^n}
\]

is the ordinary generating function that yields polynomials
expressing power sums in terms of elementary symmetric polynomials
(<https://oeis.org/A115131 OEIS A115131> or
<https://oeis.org/A210258 OEIS A210258>):

>>> map pretty $ coefficients $ (derivative ordXs * compose recipOneMinus (negate ordXs)) .* (-1)
["x1",
 "(-2)*x2 + x1^2",
 "3*x3 + (-3)*x1*x2 + x1^3",
 "(-4)*x4 + 4*x1*x3 + 2*x2^2 + (-4)*x1^2*x2 + x1^4",
 "5*x5 + (-5)*x1*x4 + (-5)*x2*x3 + 5*x1^2*x3 + 5*x1*x2^2 + (-5)*x1^3*x2 + x1^5",...

-}

{- $integer_compositions

A construction corresponding to @completeBell@, but with ordinary
generating functions, counts compositions of a non-negative integer \(n\),
or equivalently segmentations of lists of length \(n\).

The ordinary counterpart of the complete Bell polynomials
(<https://oeis.org/A048996 OEIS A048996> or
<https://oeis.org/A072811 OEIS A072811>)
is generated by the multinomial counterpart of
[Pascal's triangle](#g:polynomial_sequences):

\[
{1 \over 1 - \sum_{n=1}^\infty x_n t^n} =
	1 + \sum_{n=1}^\infty \hat B_n(x_1,\ldots, x_n) t^n
\]

This can be directly encoded:

>>> map pretty $ coefficients $ compose recipOneMinus ordXs
["1",
 "x1",
 "x2 + x1^2",
 "x3 + 2*x1*x2 + x1^3",
 "x4 + 2*x1*x3 + x2^2 + 3*x1^2*x2 + x1^4",
 "x5 + 2*x1*x4 + 2*x2*x3 + 3*x1^2*x3 + 3*x1*x2^2 + 4*x1^3*x2 + x1^5",...

In these polynomials, subscripts denote the size of each part,
superscripts denote the number of those parts, and coefficients denote
the number of ways of composing \(n\) elements into those parts.
For example, the 4th entry which says that 4 may be composed
in 1 way from one 4,
in 2 ways from 1 and 3 (1+3 and 3+1),
in 1 way from two 2s,
in 3 ways from two 1s and one 2 (1+1+2, 1+2+1 and 2+1+1), and
in 1 way from four 1s.

The ordinary counterpart of the partial Bell polynomials is generated
by \( 1 \over 1 - u \bar x (t) \), an example of a Riordan array
(see 'Data.YAP.Powerseries.riordan'):

>>> map (map pretty . Poly.coefficients) $ coefficients $ riordan one ordXs
[["1"],
 ["0","x1"],
 ["0","x2","x1^2"],
 ["0","x3","2*x1*x2","x1^3"],
 ["0","x4","2*x1*x3 + x2^2","3*x1^2*x2","x1^4"],
 ["0","x5","2*x1*x4 + 2*x2*x3","3*x1^2*x3 + 3*x1*x2^2","4*x1^3*x2","x1^5"],...

Switching from `FiniteMap` to `Data.YAP.FiniteSet.FiniteSet` would count
integer partitions.

-}

{- $noncrossing_partitions

The multinomial version of the [Narayana triangle](#g:polynomial_sequences)
satisfies

\[
A(t) = 1 + \sum_{n=1}^\infty x_n (t A(t))^n
\]

so we can define it as

>>> noncrossing = 1 + compose ordXs (mulX noncrossing)
>>> map pretty $ coefficients noncrossing
["1",
 "x1",
 "x2 + x1^2",
 "x3 + 3*x1*x2 + x1^3",
 "x4 + 4*x1*x3 + 2*x2^2 + 6*x1^2*x2 + x1^4",
 "x5 + 5*x1*x4 + 5*x2*x3 + 10*x1^2*x3 + 10*x1*x2^2 + 10*x1^3*x2 + x1^5",...

The coefficients give the number of noncrossing partitions of each type
(<https://oeis.org/A134264 OEIS A134264> or
<https://oeis.org/A125181 OEIS A125181>).

-}
