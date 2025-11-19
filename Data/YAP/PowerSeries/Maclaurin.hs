{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.PowerSeries.Maclaurin
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: power series represented as
-- sequences of derivatives at zero (Maclaurin series, or exponential
-- generating functions).
-- This representation supports the same operations as the coefficients
-- representation, but often with different constraints.  For example,
-- the derivatives may be integers while the coefficients are fractional.
--
-- * Dusko Pavlovic and M. Escardó, "Calculus in coinductive form",
--   /Thirteenth Annual IEEE Symposium on Logic in Computer Science/, 1998.
--   <http://www.isg.rhul.ac.uk/dusko/papers/1998-lapl-LICS.pdf>
--
-- * M. Douglas McIlroy, "The music of streams",
--   /Information Processing Letters/ 77 (2001) 189-195.
--
-----------------------------------------------------------------------------

module Data.YAP.PowerSeries.Maclaurin (
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
    powerRatio,
    tree,
    lambertW,
    -- ** Trigonometric functions
    sinS,
    cosS,
    secS,
    tanS,
    asinS,
    atanS,
    -- ** Hyperbolic functions
    sinhS,
    coshS,
    sechS,
    tanhS,
    asinhS,
    atanhS,

    -- * Exponential generating functions
    -- $egfs

    -- ** Binomial transform #binomial_transform#
    -- $binomial_transform

    -- ** Exponential transform
    -- $exponential_transform

    -- ** Stirling transform
    -- $stirling_transform

    -- * Polynomial sequences
    -- $polynomial_sequences
    constants,
    monomials,

    -- ** Appell sequences
    -- $appell_sequences

    -- ** Sequences of binomial type
    binomialType,
    shiftedBinomialType,

    -- ** Sheffer sequences
    -- $sheffer_sequences

    -- ** Other polynomial sequences
    -- $other_polynomial_sequences

    -- * Moment generating functions
    -- $mgf
    bernoulliMGF,
    geometricMGF,
    poissonMGF,
  ) where

import Prelude.YAP
import Data.YAP.Algebra
import qualified Data.YAP.Polynomial as Poly
import Data.YAP.Polynomial (Polynomial, RationalFunction)
import Data.YAP.Ratio
import Data.YAP.Utilities.List (longZipWith, mapOdds)

import Data.List (intersperse)
import Numeric.Natural

infixl 9 .^
infixl 9 .*

-- | Formal power series viewed as a Maclaurin series
-- \[ \sum_{n=0}^\infty f^{(n)}(0) {x^n \over n!} \]
-- represented by the sequence \(f^{(n)}(0)\) of derivatives at zero.
newtype PowerSeries a = DS [a]
    -- ^ Derivatives, least significant first.

-- | Value of the function at zero
atZero :: (AdditiveMonoid a) => PowerSeries a -> a
atZero (DS []) = zero
atZero (DS (a:_)) = a

-- Horner view: coefficients of powers of x

-- | Discard the constant term and divide by the indeterminate
divX :: (FromRational a) => PowerSeries a -> PowerSeries a
divX (DS []) = DS []
divX (DS (_:as)) = DS (zipWith (*) (map coeff (from 1)) as)
  where
    coeff n = fromRational (1%n)

-- | Multiply by the indeterminate
mulX :: (Semiring a) => PowerSeries a -> PowerSeries a
mulX (DS []) = DS []
mulX f = plusMulX zero f

-- | Multiply by the indeterminate and add @a@
plusMulX :: (Semiring a) => a -> PowerSeries a -> PowerSeries a
plusMulX a (DS as) = DS (a:zipWith atimes (from (one::Int)) as)

-- | Shift the power series by \(k\) (which may be negative): multiply
-- by \(x^k\) and discard any terms with negative exponents.
shift :: (FromRational a) => Int -> PowerSeries a -> PowerSeries a
shift _ (DS []) = DS []
shift k f
  | k >= 0 = times k mulX f
  | otherwise = times (-k) divX f

times :: Int -> (a -> a) -> a -> a
times k f = flip (foldr id) (replicate k f)

-- | The coefficients of the power series, least significant first.
coefficients :: (FromRational a) => PowerSeries a -> [a]
coefficients f = toCoefficients (derivatives f)

toCoefficients :: (FromRational a) => [a] -> [a]
toCoefficients = zipWith (*) (map coeff factorials)
  where
    coeff n = fromRational (1%n)
    factorials = scanl (*) 1 [1..]

-- | Power series formed from a list of coefficients.
-- If the list is finite, the remaining coefficients are zero.
fromCoefficients :: (Semiring a) => [a] -> PowerSeries a
fromCoefficients as = fromDerivatives (zipWith atimes factorials as)
  where
    factorials = scanl (*) (1::Integer) [1..]

-- Maclaurin view: values of repeated derivatives at zero

instance (Semiring a) => Differentiable (PowerSeries a) where
    derivative = derivativeInternal

derivativeInternal :: PowerSeries a -> PowerSeries a
derivativeInternal (DS []) = DS []
derivativeInternal (DS (_:as)) = DS as

instance (Semiring a) => Integrable (PowerSeries a) where
    integral = integralWith zero

-- | Symbolic integration of a power series, with a given value at zero.
integralWith :: a -> PowerSeries a -> PowerSeries a
integralWith a (DS as) = DS (a:as)

instance AdditiveFunctor PowerSeries where
    mapAdditive f (DS as) = DS (map f as)

-- | A list whose \(n\)th entry is the value of the \(n\)th derivative at zero.
derivatives :: (AdditiveMonoid a) => PowerSeries a -> [a]
derivatives (DS as) = as ++ repeat zero

-- | Power series formed from a list of derivatives at zero.
-- If the list is finite, the remaining derivatives are zero.
fromDerivatives :: (AdditiveMonoid a) => [a] -> PowerSeries a
fromDerivatives = foldr integralWith zero

instance (AdditiveMonoid a) => AdditiveMonoid (PowerSeries a) where
    DS as + DS bs = DS (longZipWith (+) as bs)
    zero = DS []
    atimes n p
      | n == zero = zero
      | otherwise = mapAdditive (atimes n) p

instance (AbelianGroup a) => AbelianGroup (PowerSeries a) where
    negate = mapAdditive negate
    gtimes n p
      | n == zero = zero
      | otherwise = mapAdditive (gtimes n) p

instance (Semiring a) => Semiring (PowerSeries a) where
    DS as * DS bs = DS (mul as bs)
    one = constant one
    fromNatural i = constant (fromNatural i)

-- correct, but slow, definition using the product rule:
-- f * g =
--     integralWith (atZero f*atZero g) (derivative f * g + f * derivative g)

-- multiply using the Leibniz rule
mul :: (Semiring a) => [a] -> [a] -> [a]
mul [] _ = []
mul _ [] = []
mul xs (y:ys) = mul1 (1:repeat 0) xs [y] ys

-- accumulate binomial coefficients
mul1 :: (Semiring a) => [Integer] -> [a] -> [a] -> [a] -> [a]
mul1 coeffs xs rev_ys ys =
    mulRow coeffs xs rev_ys : case ys of
        [] -> mul2' coeffs xs rev_ys
        (y:ys') -> mul1 (zipWith (+) (0:coeffs) coeffs) xs (y:rev_ys) ys'

mul2 :: (Semiring a) => [Integer] -> [a] -> [a] -> [a]
mul2 _ [] _ = []
mul2 coeffs xs rev_ys = mulRow coeffs xs rev_ys : mul2' coeffs xs rev_ys

mul2' :: (Semiring a) => [Integer] -> [a] -> [a] -> [a]
mul2' _ [] _ = []
mul2' coeffs (_:xs) rev_ys =
    mul2 (zipWith (+) coeffs (tail coeffs)) xs rev_ys

mulRow :: (Semiring a) => [Integer] -> [a] -> [a] -> a
mulRow coeffs xs rev_ys = sum (zipWith atimes coeffs (zipWith (*) xs rev_ys))

instance (Ring a) => Ring (PowerSeries a) where
    fromInteger i = constant (fromInteger i)

instance (FromRational a) => FromRational (PowerSeries a) where
    fromRational x = constant (fromRational x)

-- | Units have non-zero leading coefficients.
-- Standard associates are monomials of the form \(x^n\).
-- 'stdUnit' and 'stdRecip' are not defined on zero.
instance (Eq a, FromRational a, Field a) =>
        StandardAssociate (PowerSeries a) where
    stdAssociate = stdAssociateStream 1 1
    stdUnit = until ((/= 0) . atZero) divX
    stdRecip f = 1 `exactDiv` stdUnit f

-- scale the associate so the leading coefficient is one, matching PowerSeries
stdAssociateStream :: (Eq a, Ring a) =>
    Integer -> Integer -> PowerSeries a -> PowerSeries a
stdAssociateStream n fact_n f
  | atZero f == 0 =
    integral (stdAssociateStream (n+1) (n*fact_n) (derivative f))
  | otherwise = fromInteger fact_n

-- | @'mod' x y@ is non-zero if @y@ has more leading zeros than @x@.
-- See also 'modulus', for the remainder as a polynomial.
instance (Eq a, FromRational a, Field a) => Euclidean (PowerSeries a) where
    divMod f g = fmap fromCoefficients (divModStream f g)
    div = divStream
    mod f g = fromCoefficients (modStream f g)

    euclideanNorm (DS as) = euclideanNorm (length (takeWhile (== 0) as))

divModStream :: (Eq a, FromRational a, Field a) =>
    PowerSeries a -> PowerSeries a -> (PowerSeries a, [a])
divModStream f g
  | atZero g == 0 = (q, atZero f:r)
  | otherwise = (exactDiv f g, [])
  where
    (q, r) = divModStream (divX f) (divX g)

divStream :: (Eq a, FromRational a, Field a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries a
divStream f g
  | atZero g == 0 = divStream (divX f) (divX g)
  | otherwise = exactDiv f g

modStream :: (Eq a, FromRational a) => PowerSeries a -> PowerSeries a -> [a]
modStream f g
  | atZero g == 0 = atZero f:modStream (divX f) (divX g)
  | otherwise = []

-- | Polynomial with the first \(n\) coefficients, equivalent to the
-- remainder of division by \(x^n\).
toPolynomial :: (FromRational a) => Int -> PowerSeries a -> Polynomial a
toPolynomial n (DS as) = Poly.fromCoefficients (toCoefficients (take n as))

-- | The remainder of division by a non-zero power series is a polynomial.
modulus :: (Eq a, FromRational a) =>
    PowerSeries a -> PowerSeries a -> Polynomial a
modulus f g = Poly.fromCoefficients (modStream f g)

-- only valid if g0 is non-zero
exactDiv :: (FromRational a, Field a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries a
exactDiv f g = q
  where
    q = plusMulX (f0/g0) (constant (recip g0) * (divX f - q * divX g))
    f0 = atZero f
    g0 = atZero g

{-
-- correct, but inefficient
exactDiv f g = q
  where
    q = integralWith (atZero f/atZero g)
        (exactDiv (derivative f - q * derivative g) g)
-}

-- | Power series representing a constant value \(c\)
constant :: (AdditiveMonoid a) => a -> PowerSeries a
constant a = DS [a]

-- | Polynomial considered as a power series
fromPolynomial :: (Semiring a) => Polynomial a -> PowerSeries a
fromPolynomial p = fromCoefficients (Poly.unsafeCoefficients p)

-- | \({1 \over 1-x} = 1 + x + x^2 + \ldots \), converges for \(|x| < 1\).
-- 'derivatives' yields the factorials.
recipOneMinus :: (Semiring a) => PowerSeries a
recipOneMinus = fromCoefficients (repeat one)

-- | \(e^x = 1 + x + \frac{x^2}{2!} + \frac{x^3}{3!} + \ldots\),
-- converges everywhere.  All derivatives are 1.
expS :: (Semiring a) => PowerSeries a
expS = fromDerivatives (repeat one)

-- | \(\log {1 \over 1+x} = - \log (1 - x)\), converges for \(-1 < x \leq 1\)
logRecipOneMinus :: (Semiring a) => PowerSeries a
logRecipOneMinus = integral recipOneMinus

-- | \((1 + x)^a\), converges for \(|x| < 1\)
powerOnePlus :: (Ring a) => a -> PowerSeries a
powerOnePlus a = powerRatio (-a) (-1)

-- | \({1 \over (1 - bx)^{\frac{a}{b}}} = {1 \over {\left( \sqrt[b]{1 - bx} \right)}^a}\),
-- converges for \(|x| < 1\)
powerRatio :: (Semiring a) => a -> a -> PowerSeries a
powerRatio a b = fromDerivatives (scanl (*) one (iterate (+ b) a))

-- | \(\sin x\), converges everywhere (but faster for smaller \(x\))
sinS :: (Ring a) => PowerSeries a
sinS = fromDerivatives (cycle [0, 1, 0, -1])

-- | \(\cos x\), converges everywhere (but faster for smaller \(x\))
cosS :: (Ring a) => PowerSeries a
cosS = fromDerivatives (cycle [1, 0, -1, 0])

-- | \(\tan x\), converges for \(|x| < {\pi \over 2}\)
tanS :: (Semiring a) => PowerSeries a
-- tanS = sinS * secS -- requires Ring
tanS = fromDerivatives (map fromNatural (zeroEvens (derivatives zigzag)))

-- | \(1 \over \cos x\), converges for \(|x| < {\pi \over 2}\)
secS :: (Semiring a) => PowerSeries a
-- secS = unsafeRecipSimple cosS -- requires Ring
secS = fromDerivatives (map fromNatural (zeroOdds (derivatives zigzag)))

-- retain even positions, zero odd positions
zeroOdds :: (AdditiveMonoid a) => [a] -> [a]
zeroOdds [] = []
zeroOdds (x:xs) = x : zeroEvens xs

-- retain odd positions, zero even positions
zeroEvens :: (AdditiveMonoid a) => [a] -> [a]
zeroEvens [] = []
zeroEvens (_:xs) = zero : zeroOdds xs

-- Euler zigzag numbers defined using André's theorem
zigzag :: PowerSeries Natural
zigzag = integralWith one (mapAdditive (`div` two) (zigzag*zigzag + one))
  where
    two = one+one

-- | \(\sin^{-1} x\), converges for \(|x| \leq 1\)
asinS :: (Semiring a) => PowerSeries a
asinS = integral $ fromDerivatives $ intersperse zero oeisA001818
-- fromDerivatives OEIS A177145 = spaced A001818

-- | Squared double factorials (OEIS A001818)
oeisA001818 :: (Semiring a) => [a]
oeisA001818 = [f*f | f <- doubleFactorials]

-- | Double factorials (OEIS A001147):
-- (2n-1)!! = 1*3*5*...*(2n-1) = (2n)!/2^n/n!
doubleFactorials :: (Semiring a) => [a]
doubleFactorials = scanl (*) one (iterate (+ (one+one)) one)
-- derivatives $ powerRatio 1 (-2)

-- | \(\tan^{-1} x\), converges for \(|x| \leq 1\)
atanS :: (Ring a) => PowerSeries a
atanS = integral (fromCoefficients (cycle [1, 0, -1, 0]))
-- atanS = integral (recipOneMinus .* (-1) .^ 2)

-- | \(\sinh x\), converges everywhere (but faster for smaller \(x\))
sinhS :: (Semiring a) => PowerSeries a
sinhS = fromDerivatives (cycle [zero, one])

-- | \(\cos x\), converges everywhere (but faster for smaller \(x\))
coshS :: (Semiring a) => PowerSeries a
coshS = fromDerivatives (cycle [one, zero])

-- | \(\tanh x\), converges for \(|x| < {\pi \over 2}\)
tanhS :: (Ring a) => PowerSeries a
tanhS = sinhS * sechS

-- | \(1 \over \cosh x\), converges for \(|x| < {\pi \over 2}\)
sechS :: (Ring a) => PowerSeries a
sechS = unsafeRecipSimple coshS

-- | \(\sinh^{-1} x\), converges for \(|x| \leq 1\)
asinhS :: (Ring a) => PowerSeries a
asinhS =
    integral $ fromDerivatives $ intersperse zero $ mapOdds negate oeisA001818

-- | \(\tanh^{-1} x\), converges for \(|x| < 1\)
atanhS :: (Semiring a) => PowerSeries a
atanhS = integral (fromCoefficients (cycle [one, zero]))

-- | The infinite list of evaluations of truncations of the power series.
approximations :: (FromRational a) => PowerSeries a -> a -> [a]
approximations = approximationsWith (*)

-- | The infinite list of evaluations of truncations of the power series,
-- given a function to combine coefficients and powers.
approximationsWith :: (FromRational a, Semiring b, AdditiveMonoid c) =>
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
padeApproximants :: (Eq a, FromRational a, Field a) =>
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
  | atZero f == atZero g =
    countSame (derivativeInternal f) (derivativeInternal g) + 1
  | otherwise = 0

from :: (Semiring a) => a -> [a]
from = iterate (+one)

-- | Identity function, i.e. the indeterminate
identity :: (Semiring a) => PowerSeries a
identity = integral one

-- | composition \(f(g(x))\). This is only defined if \(g_0\) is 0.
compose :: (Eq a, Semiring a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries a
compose f g
  | atZero g /= zero =
    error "compose: second series has non-zero constant term"
  | otherwise = composeIntegral f (derivative g)

-- | Special composition \(f(\int_0^x g(u) du)\).
composeIntegral :: (Semiring a) =>
    PowerSeries a -> PowerSeries a -> PowerSeries a
composeIntegral f g =
    integralWith (atZero f) (g * composeIntegral (derivative f) g)

-- | pre-inverse under 'compose':
--
-- * @'compose' f ('inverse' f) = 'identity'@
--
-- This is only defined if \(f_0\) is zero and \(f_1\) is non-zero.
inverse :: (Eq a, FromRational a, Field a) => PowerSeries a -> PowerSeries a
inverse f
  | atZero f /= 0 = error "inverse: zero constant term"
  | atZero (derivative f) == 0 = error "inverse: non-zero linear term"
  | otherwise = unsafeInverse f

-- assumes \(f_0\) is zero and \(f_1\) is non-zero.
unsafeInverse :: (FromRational a, Field a) => PowerSeries a -> PowerSeries a
unsafeInverse f = r
  where
    r = integral (1 `exactDiv` composeIntegral (derivative f) (derivative r))

-- | Special case of 'inverse' that is only valid if the coefficient of
-- the linear term is 1.
inverseSimple :: (Eq a, Ring a) => PowerSeries a -> PowerSeries a
inverseSimple p = r
  where
    r = integral (recipSimple (composeIntegral (derivative p) (derivative r)))

-- | Maps a function \(f(x)\) to \(f(a x)\), equivalent to composition
-- with @a*'identity'@.
(.*) :: (Semiring a) => PowerSeries a -> a -> PowerSeries a
DS as .* a = DS (zipWith (*) as (iterate (*a) one))

-- | Maps a function \(f(x)\) to \(f(x^k)\) for positive \(k\), equivalent
-- to composition with @'identity'^k@.
(.^) :: (Semiring a) => PowerSeries a -> Int -> PowerSeries a
DS as .^ k
  | k <= 0 = error "non-positive power"
  | k == 1 = DS as
DS [] .^ _ = DS []
DS (a:as) .^ k =
    DS (a:concat [padding ++ [atimes (factor n) a'] | (n, a') <- zip [1..] as])
  where
    factor n = product [n+1..k*n]
    padding = replicate (k-1) zero

-- | Special case of 'recip' that is only valid if the constant term is 1.
recipSimple :: (Eq a, Ring a) => PowerSeries a -> PowerSeries a
recipSimple p = compose recipOneMinus (1 - p)

unsafeRecipSimple :: (Ring a) => PowerSeries a -> PowerSeries a
unsafeRecipSimple p = composeIntegral recipOneMinus (- derivative p)

-- | Special case of division that is only valid if the constant term
-- of the divisor is 1.
divSimple :: (Eq a, Ring a) => PowerSeries a -> PowerSeries a -> PowerSeries a
divSimple p q = p * recipSimple q

-- Exponential generating functions

{- $egfs
This representation corresponds to viewing
a power series \( \sum_{n=0}^\infty a_n {x^n \over n!} \)
as the exponential generating function of a sequence \( \{a_n\} \).
The corresponding sequence may be extracted using 'derivatives'.

=== Examples

* /Euler zigzag numbers/, the number of alternating permutations of \(n\)
elements (<https://oeis.org/A000111 OEIS A000111>) have the exponential
generating function \( \sec x + \tan x \):

>>> derivatives $ secS + tanS
[1,1,1,2,5,16,61,272,1385,7936,50521,353792,2702765,22368256,...

* Double factorials of odd numbers (<https://oeis.org/A001147 OEIS A001147>)
have the exponential generating function \( 1 \over \sqrt{1 - 2x}\):

>>> derivatives $ powerRatio 1 2
[1,1,3,15,105,945,10395,135135,2027025,34459425,654729075,...

* /Bernoulli numbers/ (<https://oeis.org/A027641 OEIS A027641> /
<https://oeis.org/A027642 OEIS A027642>) have the exponential
generating function \(x \over e^x - 1\):

>>> derivatives $ identity `div` integral expS
[1 % 1,(-1) % 2,1 % 6,0 % 1,(-1) % 30,0 % 1,1 % 42,0 % 1,(-1) % 30,0 % 1,...

* The alternative convention, differing only in the sign of \(B_1\),
has the exponential
generating function \(x + {x \over e^x - 1} = {x e^x \over e^x - 1}\):

>>> derivatives $ identity*expS `div` integral expS
[1 % 1,1 % 2,1 % 6,0 % 1,(-1) % 30,0 % 1,1 % 42,0 % 1,(-1) % 30,0 % 1,...

We can use 'div' here, because it divides evenly when the numerator has
at least as many leading non-zero terms as the denominator.

-}

-- Number sequences

{- $binomial_transform

Multiplying the exponential generating function of a sequence \( \{a_n\} \)
by \(e^x\) yields the exponential generating function of the sequence

\[
    b_n = \sum_{k=0}^{n} \binom{n}{k} a_k
\]

The same transformation on sequences from ordinary generating functions
is performed by `Data.YAP.PowerSeries.binomialTransform`.

The inverse transformation, namely

\[
    a_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} b_k
\]

is obtained by multiplying by \(e^{ -x}\).
The same transformation on sequences from ordinary generating functions
is performed by `Data.YAP.PowerSeries.inverseBinomialTransform`.

=== Examples

* Maximal number of pieces obtained by cutting a circle with \(n\) lines
(<https://oeis.org/A000124 OEIS A000124>).

>>> derivatives $ expS*fromDerivatives [1,1,1]
[1,2,4,7,11,16,22,29,37,46,56,67,79,92,106,121,137,154,172,191,211,232,...

* Maximal number of pieces obtained by cutting a sphere with \(n\) planes
(<https://oeis.org/A000125 OEIS A000125>).

>>> derivatives $ expS*fromDerivatives [1,1,1,1]
[1,2,4,8,15,26,42,64,93,130,176,232,299,378,470,576,697,834,988,1160,...

* Maximal number of regions obtained by the straight lines joining \(n\)
points around a circle (<https://oeis.org/A000127 OEIS A000127>).

>>> derivatives $ expS*fromDerivatives [1,1,1,1,1]
[1,2,4,8,16,31,57,99,163,256,386,562,794,1093,1471,1941,2517,3214,...

-}

{- $exponential_transform

If \(a(x)\) is the exponential generating function of a sequence \(\{a_n\}\)
with \(a_0 = 0\), then \(e^{a(x)}\) is the exponential generating function
of the sequence

\[
    b_n = \sum_{k=1}^{n} B_n(a_1, \ldots, a_n)
\]

where \(B_n\) are complete Bell polynomials
(see "Data.YAP.FiniteMap#g:Bell_polynomials").

=== Examples

* /Bell numbers/, the number of ways to partition \(n\) elements
(<https://oeis.org/A000110 OEIS A000110>) have the exponential
generating function \(e^{e^x - 1}\).
Using @'integral' 'expS'@ instead of the equivalent @'expS' - 1@
avoids requiring subtraction:

>>> derivatives $ expS `compose` integral expS
[1,1,2,5,15,52,203,877,4140,21147,115975,678570,...

* The number of ways to partition \(n\) elements into sets of at least
two elements (<https://oeis.org/A000296 OEIS A000296>) has the exponential
generating function \(e^{e^x - x - 1}\).

>>> derivatives $ expS `compose` integral (integral expS)
[1,0,1,1,4,11,41,162,715,3425,17722,98253,580317,3633280,...

* The number of ways of partitioning \(n\) elements into lists
(<https://oeis.org/A000262 OEIS A000262>) has the exponential
generating function \(e^{x \over x - 1}\):

>>> derivatives $ expS `compose` (identity * recipOneMinus)
[1,1,3,13,73,501,4051,37633,394353,4596553,58941091,824073141,...

* /Hermite numbers/ (<https://oeis.org/A067994 OEIS A067994>) have
the exponential generating function \(e^{ -x^2}\):

>>> derivatives $ expS `compose` (- identity^2)
[1,0,-2,0,12,0,-120,0,1680,0,-30240,0,665280,0,-17297280,0,...

-}

{- $stirling_transform

If \(a(x)\) is the exponential generating function of a sequence \( \{a_n\} \),
then \(a(e^x-1)\) is the exponential generating function of the sequence

\[
    b_n = \sum_{k=0}^n S(n, k) a_k
\]

where the coefficients \(S(n,k)\) are Stirling numbers of the second
kind (<https://oeis.org/A048993 OEIS A048993>).

The inverse transform \(b(\log (x+1))\) has exponential generating function

\[
    a_n = \sum_{k=0}^n s(n, k) b_k
\]

where the coefficients \(s(n,k)\) are Stirling numbers of the first
kind (<https://oeis.org/A048994 OEIS A048994>).

=== Examples

* The expression for the /Bell numbers/ given above is also a Stirling
transform of \(e^x\):

>>> derivatives $ expS `compose` integral expS
[1,1,2,5,15,52,203,877,4140,21147,115975,678570,...

* The Stirling transform of \(x e^x\) generates the /2-Bell numbers/
(<https://oeis.org/A005493 OEIS A005493>):

>>> derivatives $ mulX expS `compose` integral expS
[0,1,3,10,37,151,674,3263,17007,94828,562595,3535027,23430840,...

* The Stirling transform of \(\cosh x\) generates the number of partitions
of \(n\) elements into an even number of classes
(<https://oeis.org/A024430 OEIS A024430>):

>>> derivatives $ coshS `compose` integral expS
[1,0,1,3,8,25,97,434,2095,10707,58194,338195,2097933,13796952,...

* The Stirling transform of \(\sinh x\) generates the number of partitions
of \(n\) elements into an odd number of classes
(<https://oeis.org/A024429 OEIS A024429>):

>>> derivatives $ sinhS `compose` integral expS
[0,1,1,2,7,27,106,443,2045,10440,57781,340375,2115664,13847485,...

* /Fubini numbers/, the number of weak orders on \(n\) elements
(<https://oeis.org/A000670 OEIS A000670>) have the exponential
generating function \( {1 \over 2 - e^x} = {1 \over 1 - (e^x - 1)} \),
i.e. the Stirling transform of \( 1 \over 1-x \):

>>> derivatives $ recipOneMinus `compose` integral expS
[1,1,3,13,75,541,4683,47293,545835,7087261,102247563,1622632573,...

-}

-- | Euler tree function, defined as
--
-- \[ T(x) = \sum_{n=1}^\infty n^{n-1} {x^n \over n!} \]
--
-- The \(n\)th coefficient is the number of labelled trees with \(n\)
-- nodes (<https://oeis.org/A152917 OEIS A152917>).
--
-- \(T\) satisfies \(T(x) = x e^{T(x)}\).
-- It is thus the inverse of \( y e^{ - y} \).
--
-- \(T\) is the unsigned version of the
-- Lambert \(W\) function: \(T(x) = -W(-x) \).
tree :: (Semiring a) => PowerSeries a
tree = fromDerivatives (zero : [fromNatural (n+one)^n | n <- from zero])

-- | Lambert \(W\) function, the inverse of \(x e^x\), equal to \(-T(-x)\).
-- The series converges for \(|x| < \frac{1}{e}\).
lambertW :: (Ring a) => PowerSeries a
lambertW = - (tree .* (-1))

-- Polynomial sequences

{- $polynomial_sequences
A polynomial sequence is a sequence of polynomials \(\{p_n(x)\}\)
where each polynomial \(p_n\) has degree at most \(n\), so that
the coefficients form a triangle.  Such sequences can be defined
by exponential generating functions of the form

\[
    \sum_{n=0}^\infty p_n(x) {t^n \over n!}
\]
-}

-- | Promotion of a power series to a power series of constant polynomials
constants :: (AdditiveMonoid a) => PowerSeries a -> PowerSeries (Polynomial a)
constants f = mapAdditive Poly.constant f

-- | \(e^{xt}\), the exponential generating function for the sequence of
-- monomials \(\{x^n\}\)
monomials :: (Eq a, Semiring a) => PowerSeries (Polynomial a)
monomials = expS .* Poly.identity

{- $appell_sequences
An Appell sequence is a polynomial sequence with an exponential generating
function of the form \(a(t)e^{xt}\), which can be constructed as
@`constants` a * `monomials`@.

* Substituting \(x = 0\) shows that the original sequence is included as
  the constant terms of the polynomial sequence.

* Substituting \(x = 1\) shows that the sequence of sums of coefficients of
  the polynomials is generated by \(a(t)e^t\),
  the binomial transform of \(a(t)\).

If \(a(t)\) is an exponential generating function for a sequence \(\{a_n\}\),
then \(a(t) e^{xt}\) is the exponential generating function for
the polynomial sequence \(\{p_n(x)\}\) where

\[
	p_n(x) = \sum_{k=0}^n {n \choose k} a_{n-k} x^k
\]

==== Examples

The exponential generating function \(e^{(1+x)t} = e^t e^{xt}\) yields
a sequence of polynomials with binomial coefficients
(Pascal's triangle, <https://oeis.org/A007318 OEIS A007318>):

>>> derivatives $ constants expS * monomials
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,2,1],
 fromCoefficients [1,3,3,1],
 fromCoefficients [1,4,6,4,1],
 fromCoefficients [1,5,10,10,5,1],...

The exponential generating function \(2 e^{xt} \over e^t + 1\) yields
Euler polynomials (<https://oeis.org/A060096 OEIS A060096> /
<https://oeis.org/A060097 OEIS A060097>):

>>> derivatives $ constants (2 `div` (expS + 1)) * monomials
[fromCoefficients [1 % 1],
 fromCoefficients [(-1) % 2,1 % 1],
 fromCoefficients [0 % 1,(-1) % 1,1 % 1],
 fromCoefficients [1 % 4,0 % 1,(-3) % 2,1 % 1],
 fromCoefficients [0 % 1,1 % 1,0 % 1,(-2) % 1,1 % 1],
 fromCoefficients [(-1) % 2,0 % 1,5 % 2,0 % 1,(-5) % 2,1 % 1],...

The exponential generating function \(t e^{xt} \over e^t - 1\) yields
Bernoulli polynomials (<https://oeis.org/A196838 OEIS A196838> /
<https://oeis.org/A196839 OEIS A196839>):

>>> derivatives $ constants (identity `div` (expS - 1)) * monomials
[fromCoefficients [1 % 1],
 fromCoefficients [(-1) % 2,1 % 1],
 fromCoefficients [1 % 6,(-1) % 1,1 % 1],
 fromCoefficients [0 % 1,1 % 2,(-3) % 2,1 % 1],
 fromCoefficients [(-1) % 30,0 % 1,1 % 1,(-2) % 1,1 % 1],...

-}

{- | An exponential generating function for a polynomial sequence of
binomial type has the form \(e^{x b(t)}\) with \(b_0\) zero and \(b_1\)
non-zero, which can be constructed as @`compose` `monomials` (`constants` b)@.

Substituting \(x = 1\) shows that the sequence of sums of coefficients of
the polynomials is generated by the exponential transform of \(b(t)\).
Indeed a polynomial sequence of binomial type can be viewed as the
exponential transform of \(b(t)\) raised to the
power \(x\): \(e^{x b(t)} = {\left(e^{b(t)}\right)}^x\).

If \(b(t)\) is an exponential generating function for a sequence \(\{b_n\}\),
with \( b_0 = 0 \),
then \(e^{x b(t)}\) is the exponential generating function for
the polynomial sequence \(\{p_n(x)\}\) where

\[
	p_n(x) = \sum_{k=0}^n B_{n,k}(b_1,\ldots,b_{n-k+1}) x^k
\]

where \(B_{n,k}\) are partial Bell polynomials
(see "Data.YAP.FiniteMap#g:Bell_polynomials").
The original sequence is included as the coefficients of \(x^1\) in the
polynomial sequence.

==== __Examples__

The sequence of rising factorial polynomials has the exponential
generating function

\[
	\sum_{n=0}^\infty
		\left( \sum_{k=0}^n c(n,k) x^k \right) \frac{t^n}{n!}
	= {1 \over (1-t)^x}
	= e^{x \log {1 \over 1-t}}
\]

where the coefficients \(c(n,k)\) are unsigned Stirling numbers of the
first kind (<https://oeis.org/A132393 OEIS A132393>), the number of
permutations of \(n\) elements that have exactly \(k\) cycles.

>>> derivatives $ binomialType logRecipOneMinus
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,2,3,1],
 fromCoefficients [0,6,11,6,1],
 fromCoefficients [0,24,50,35,10,1],...

The usual Stirling numbers of the first kind \(s(n,k)\)
(<https://oeis.org/A048994 OEIS A048994>) are the coefficients of the
sequence of falling factorial polynomial, which have the exponential
generating function \( e^{x \log(1 + t)} \):

>>> derivatives $ binomialType $ negate $ logRecipOneMinus .* (-1)
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,-1,1],
 fromCoefficients [0,2,-3,1],
 fromCoefficients [0,-6,11,-6,1],
 fromCoefficients [0,24,-50,35,-10,1],...

The sequence of Touchard polynomials has the exponential generating function

\[
	\sum_{n=0}^\infty
		\left( \sum_{k=0}^n S(n,k) x^k \right) \frac{t^n}{n!}
	= e^{x (e^t - 1)}
	= e^{x \int_0^t e^u du}
\]

where the coefficients \(S(n,k)\) are Stirling numbers of the second
kind (<https://oeis.org/A048993 OEIS A048993>), the number of ways to
partition a set of \(n\) elements into \(k\) non-empty subsets.

>>> derivatives $ binomialType (integral expS)
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,1],
 fromCoefficients [0,1,3,1],
 fromCoefficients [0,1,7,6,1],
 fromCoefficients [0,1,15,25,10,1],...

The sequence of unsigned Mahler polynomials has the exponential generating
function

\[ e^{x (e^t - t - 1)} \]

where the coefficients are second-order Stirling numbers
(<https://oeis.org/A358623 OEIS A358623>).

>>> derivatives $ binomialType (integral $ integral expS)
[fromCoefficients [1],
 fromCoefficients [],
 fromCoefficients [0,1],
 fromCoefficients [0,1],
 fromCoefficients [0,1,3],
 fromCoefficients [0,1,10],
 fromCoefficients [0,1,25,15],
 fromCoefficients [0,1,56,105],
 fromCoefficients [0,1,119,490,105],
 fromCoefficients [0,1,246,1918,1260],...

The exponential generating function

\[
	\sum_{n=0}^\infty
		\left( \sum_{k=0}^n L(n,k) x^k \right) \frac{t^n}{n!}
	= e^{xt \over 1-t}
\]

defines a series of polynomials where the coefficients \(L(n,k)\)
are unsigned Lah numbers (<https://oeis.org/A271703 OEIS A271703>),
the number of ways to partition a set of \(n\) elements into \(k\)
non-empty ordered subsets.

>>> derivatives $ binomialType (identity * recipOneMinus)
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,2,1],
 fromCoefficients [0,6,6,1],
 fromCoefficients [0,24,36,12,1],
 fromCoefficients [0,120,240,120,20,1],...

The sequence of Abel polynomials (<https://oeis.org/A137452 OEIS A137452>)
has the exponential generating function \( e^{x W(t)} = e^{ - x T(-t)} \).

>>> derivatives $ binomialType lambertW
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,-2,1],
 fromCoefficients [0,9,-6,1],
 fromCoefficients [0,-64,48,-12,1],
 fromCoefficients [0,625,-500,150,-20,1],...

The sequence of tree polynomials has the exponential generating function

\[
	\sum_{n=0}^\infty
		\left( \sum_{k=0}^n T(n,k) x^k \right) \frac{t^n}{n!}
	= {1 \over (1-T(t))^x}
	= e^{x \log {1 \over 1-T(t)}}
\]

where \(T(n, k)\) (<https://oeis.org/A060281 OEIS A060281>) is the number
of endofunctions on a set of size \(n\) with exactly \(k\) cycles.

>>> derivatives $ binomialType (integral recipOneMinus `compose` tree)
[fromCoefficients [1],
 fromCoefficients [0,1],
 fromCoefficients [0,3,1],
 fromCoefficients [0,17,9,1],
 fromCoefficients [0,142,95,18,1],
 fromCoefficients [0,1569,1220,305,30,1],...

The sum of each row is \(n^n\) (<https://oeis.org/A000312 OEIS A000312>),
which has exponential generating function \({1 \over 1-T(t)}\):

>>> derivatives $ compose recipOneMinus tree
[1,1,4,27,256,3125,46656,823543,16777216,387420489,10000000000,...

-}
binomialType :: (Eq a, Semiring a) =>
    PowerSeries a -> PowerSeries (Polynomial a)
binomialType f = compose expS (mapAdditive Poly.linear f)

{- | Polynomial sequences of binomial type, generated by \(e^{xb(t)}\),
consist of polynomial with zero constant part, except the first entry,
which is 1.  Thus we may be interested in a shifted version, with
exponential generating function

\[
    \frac{1}{x} \frac{d}{dt} e^{xb(t)} = b'(t) e^{xb(t)}
\]

==== __Examples__

A shifted version of the Touchard polynomials above is
generated by \(e^t e^{e(e^t - 1})\):

>>> derivatives $ shiftedBinomialType (integral expS)
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,3,1],
 fromCoefficients [1,7,6,1],
 fromCoefficients [1,15,25,10,1],
 fromCoefficients [1,31,90,65,15,1],...

The reverse Bessel polynomials (<https://oeis.org/A001497 OEIS A001497>)
are generated by

\[
    \frac{1}{\sqrt{1 - 2t}} e^{x(1-\sqrt{1 - 2t})}
\]

>>> derivatives $ shiftedBinomialType (1 - powerRatio (-1) 2)
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [3,3,1],
 fromCoefficients [15,15,6,1],
 fromCoefficients [105,105,45,10,1],
 fromCoefficients [945,945,420,105,15,1],
 fromCoefficients [10395,10395,4725,1260,210,21,1],
 fromCoefficients [135135,135135,62370,17325,3150,378,28,1],
 fromCoefficients [2027025,2027025,945945,270270,51975,6930,630,36,1],...

-}
shiftedBinomialType :: (Eq a, Semiring a) =>
    PowerSeries a -> PowerSeries (Polynomial a)
shiftedBinomialType f = constants (derivative f) * binomialType f

{- $sheffer_sequences

A generalization of Appell sequences and sequences of binomial type is
Sheffer sequences (or exponential Riordan arrays), which have exponential
generating functions of the form

\[
    \sum_{n=0}^\infty p_n(x) {t^n \over n!} = a(t) e^{x b(t)}
\]

where \(b_0\) is zero and \(a_0\) and \(b_1\) are non-zero,
which can be constructed as @`constants` a * `binomialType` b@.

Setting \(x = 1\) yields \( a(t) e^{b(t)} \), the exponential
generating function of the sequence of sums of the coefficients of
the rows.

==== Examples

The Hermite polynomials (<https://oeis.org/A060821 OEIS A060821>)
have the exponential generating function

\[
    \sum_{n=0}^\infty H_n(x) {t^n \over n!} = e^{2xt - t^2} = e^{ -t^2} e^{2xt}
\]

>>> derivatives $ constants (expS .* (-1) .^ 2) * binomialType (2*identity)
[fromCoefficients [1],
 fromCoefficients [0,2],
 fromCoefficients [-2,0,4],
 fromCoefficients [0,-12,0,8],
 fromCoefficients [12,0,-48,0,16],
 fromCoefficients [0,120,0,-160,0,32],...

A variant of the Lah polynomials above yields the unsigned Laguerre
polynomials, with exponential generating function

\[
	e^{xt \over 1-t} \over 1-t
\]

whose coefficents are the number of partial bijections of height \(k\)
on an \(n\)-element set, or equivalently the number of ways to place \(k\)
rooks on an \(n \times n\) chessboard with none attacking another
(<https://oeis.org/A144084 OEIS A144084>):

>>> derivatives $ constants recipOneMinus * binomialType (identity * recipOneMinus)
[fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [2,4,1],
 fromCoefficients [6,18,9,1],
 fromCoefficients [24,96,72,16,1],
 fromCoefficients [120,600,600,200,25,1],...

-}

{- $other_polynomial_sequences

The sequence of Eulerian polynomials has the exponential generating function

\[
	\sum_{n=0}^\infty
		\left( \sum_{k=0}^n A(n,k) x^k \right) \frac{t^n}{n!}
	= {x - 1 \over x - e^{(x-1)t}}
	= {1 \over 1 - {e^{(x-1)t} - 1 \over x - 1}}
\]

where the coefficients \(A(n,k)\) are the
Eulerian numbers (<https://oeis.org/A008292 OEIS A008292>),
the number of permutations of the numbers 1 to \(n\) in
which exactly \(k\) elements are greater than the previous element:

>>> import qualified Data.YAP.Polynomial as Poly
>>> derivatives $ recipOneMinus `compose` integral (expS .* Poly.fromCoefficients [-1, 1])
[fromCoefficients [1],
 fromCoefficients [1],
 fromCoefficients [1,1],
 fromCoefficients [1,4,1],
 fromCoefficients [1,11,11,1],
 fromCoefficients [1,26,66,26,1],...

All polynomials after the first have a leading coefficient of @0@,
which is not shown.

Faulhaber's formula expresses the sum \(\sum_{k=1}^n k^p\) as a polynomial
of degree \(p+1\) in \(n\).  For example,

\[
    \begin{align}
	\sum_{k=1}^n k^0 & = n \\
	\sum_{k=1}^n k^1 & = {n(n+1) \over 2} = {n^2 \over 2} + {n \over 2} \\
	\sum_{k=1}^n k^2 & = {n(n+1)(2n+1) \over 6}
		= {n^3 \over 3} + {n^2 \over 2} + {n \over 6}
    \end{align}
\]

The exponential generating function for this polynomial sequence
 (<https://oeis.org/A220962 OEIS A220962> /
<https://oeis.org/A220963 OEIS A220963>) is

\[
	\int_0^t e^u {e^{xu} - 1 \over e^u - 1} du
\]

>>> derivatives $ integral $ constants (mulX expS `div` (expS - 1)) * divX (monomials - 1)
[fromCoefficients [],
 fromCoefficients [0 % 1,1 % 1],
 fromCoefficients [0 % 1,1 % 2,1 % 2],
 fromCoefficients [0 % 1,1 % 6,1 % 2,1 % 3],
 fromCoefficients [0 % 1,0 % 1,1 % 4,1 % 2,1 % 4],
 fromCoefficients [0 % 1,(-1) % 30,0 % 1,1 % 3,1 % 2,1 % 5],
 fromCoefficients [0 % 1,0 % 1,(-1) % 12,0 % 1,5 % 12,1 % 2,1 % 6],...

(This expression uses 'mulX' and 'divX' to introduce cancelling factors
so that the 'div' divides exactly.)

-}

{- $mgf
The moment generating function of a random variable \(X\) is

\[
    E[e^{tX}] = \sum_{n=0}^\infty m_n {t^n \over n!}
\]

where \(m_n\) is the \(n\)th moment of the distribution of \(X\).

* `one` is the MGF for the constant random variable with value 0.

* `expS` is the MGF for the constant random variable with value 1.

* If @pX@ is the MGF for the random variable \(X\), then the MGF for
  \(c X\) is @pX .* c@.

* The product of MGFs for independent random variables \(X\) and \(Y\)
  is the MGF for \(X+Y\).

* If a natural number valued random variable \(X\) has probability
  generating function \(f\) (see "Data.YAP.PowerSeries#g:PGF"),
  then its MGF is \(f(e^t)\).  We can't express this using 'compose'
  (because the constant term of \(e^t\) is non-zero), but can often find
  an equivalent expression.

* The logarithm of the moment generating function of a distribution is
  its cumulant generating function.
-}

-- | The distribution of a single Bernoulli trial with probability \(p\)
-- of success has moment generating function \((1-p) + p e^t\).
--
-- Powers of this distribution yield the binomial distribution.
bernoulliMGF :: (Ring a) => a -> PowerSeries a
bernoulliMGF p = constant (1-p) + constant p * expS

-- | The geometric distribution, of the number of Bernoulli trials with
-- probability \(p\) before the first success,
-- has moment generating function \( {p \over 1 - (1-p)e^t} \).
--
-- Powers of this distribution yield the negative binomial or Pascal
-- distribution.
geometricMGF :: (Eq a, Ring a) => a -> PowerSeries a
geometricMGF p = divSimple (constant p) (1 - constant (1-p) * expS)

-- | The Poisson distribution with parameter \(\lambda\), of the number
-- of events with mean rate \(\lambda\) occurring in an interval,
-- has moment generating function \( e^{\lambda(e^t-1)} \).
poissonMGF :: (Eq a, Floating a) => a -> PowerSeries a
poissonMGF l = compose (expS .* l) (expS - 1)
