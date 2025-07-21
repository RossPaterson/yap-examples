{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Quadratic.Dirichlet
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: Dirichlet integers
-- (a real quadratic integer ring).
--
-----------------------------------------------------------------------------

module Data.YAP.Quadratic.Dirichlet (
    Dirichlet(..),
    -- * Construction
    inject,
    phi,
    phiPower,
    sqrt5,
    -- * Queries
    stdUnitParts,
    toReal,
    norm,
    -- * Conjugate
    conjugate,
    ) where

import Prelude.YAP
import Data.YAP.Algebra

-- | D a b represents \(a + b\phi\), where \(\phi = {1 + \sqrt 5 \over 2}\)
-- (the golden ratio).
-- When \(a\) and \(b\) are integers, this is equivalent to
-- the ring \({\Bbb Z}(\phi)\) of algebraic integers of
-- the real quadratic field \({\Bbb Q}(\sqrt 5)\).
data Dirichlet a = D a a
    deriving (Eq, Show)

instance Functor Dirichlet where
    fmap f (D a b) = D (f a) (f b)

instance (AdditiveMonoid a) => AdditiveMonoid (Dirichlet a) where
    D a b + D c d = D (a+c) (b+d)
    zero = inject zero
    atimes n = fmap (atimes n)

instance (AbelianGroup a) => AbelianGroup (Dirichlet a) where
    negate = fmap negate
    gtimes n = fmap (gtimes n)

instance (Semiring a) => Semiring (Dirichlet a) where
    D a b * D c d = D (a*c + b*d) (a*d + b*c + b*d)
    one = inject one
    fromNatural a = inject (fromNatural a)

instance (Ring a) => Ring (Dirichlet a) where
    fromInteger a = inject (fromInteger a)

-- | If @y@ is non-zero, @'mod' x y@ has a smaller absolute norm than @y@.
instance (Integral a) => Euclidean (Dirichlet a) where
    x `div` y = round_div (x * conjugate y) (norm y)
      where
        round_div (D a b) n = D (round_div_int a n) (round_div_int b n)
        round_div_int i n = (2*i + n) `div` (2*n)
    x `mod` y = x - y*(x `div` y)
    divMod x y = (q, x - y*q)
      where q = x `div` y

    euclideanNorm = euclideanNorm . norm

instance (FromRational a) => FromRational (Dirichlet a) where
    fromRational a = inject (fromRational a)

-- | Inject the rational part.
inject :: (AdditiveMonoid a) => a -> Dirichlet a
inject a = D a zero

-- | Units have the form \( \pm\phi^n \) for integer \(n\) (possibly
-- negative).  If @x@ is non-zero, @'stdAssociate' x@ has the form @D a b@
-- where @0 <= b < a@.
instance (Ring a, ToInteger a) => StandardAssociate (Dirichlet a) where
    stdUnit x = unit (stdUnitParts x)
    stdRecip x = unit (fmap negate (stdUnitParts x))

instance (Field a) => DivisionSemiring (Dirichlet a) where
    recip x = fmap (/ norm x) (conjugate x)

instance (Field a) => Semifield (Dirichlet a)

instance (Field a) => DivisionRing (Dirichlet a)

instance (Field a) => Field (Dirichlet a)

unit :: (Ring a) => (Bool, Int) -> Dirichlet a
unit (neg, k) = sign phi_k
  where
    sign = if neg then negate else id
    phi_k
      | k < 0 = (phi - 1)^(-k)
      | otherwise = phi^k

-- | @'stdUnit' x@ decomposed as a sign ('True' means negative) and a
-- power of \(\phi\).
stdUnitParts :: (Ord a, Ring a) => Dirichlet a -> (Bool, Int)
stdUnitParts x@(D a b)
  | nx > 0 && a > 0 = (False, unit_simple x)
  | nx > 0 && a < 0 = (True, unit_simple (negate x))
  | nx < 0 && b > 0 = (False, unit_simple (phi*x) - 1)
  | nx < 0 && b < 0 = (True, unit_simple (phi*negate x) - 1)
  | otherwise = (False, 0)
  where
    nx = norm x

-- Assuming the value is in the right quadrant, return the power of phi.
-- The power must be even, so at each stage we multiply or divide by phi^2.
-- This could be sped up with an exponential/binary search.
unit_simple :: (Ord a, Ring a) => Dirichlet a -> Int
unit_simple x@(D a b)
  | b < 0 = unit_simple (x * D 1 1) - 2
  | b >= a = unit_simple (x * D 2 (-1)) + 2
  | otherwise = 0

-- | The Dirichlet integer representing \( \sqrt 5 = 2\phi - 1 \).
sqrt5 :: (Ring a) => Dirichlet a
sqrt5 = D (-1) 2

-- | The golden ratio \(\phi = {1 + \sqrt 5 \over 2}\), which is the
-- fundamental unit of \({\Bbb Z}(\phi)\).
phi :: (Semiring a) => Dirichlet a
phi = D zero one

-- | The \(n\)th power of \(\phi\),
-- satisfying \( \phi^n = F_{n-1} + F_n \phi \),
-- where \(F_n\) is the \(n\)th Fibonacci number.
phiPower :: (Ring a, Integral n) => n -> Dirichlet a
phiPower n
  | n == 0 = 1
  | n < 0 = (phi - 1)^(-n)
  | otherwise = phi^n

-- | The corresponding real number
toReal :: (Floating a) => Dirichlet a -> a
toReal (D a b) = a + (1 + sqrt 5)/2*b

-- | Conjugate of a Dirichlet integer, satisfying
--
-- * @'conjugate' ('conjugate' x) = x@
--
-- * @'conjugate' ('inject' n) = 'inject' n@
conjugate :: (AbelianGroup a) => Dirichlet a -> Dirichlet a
conjugate (D a b) = D (a+b) (-b)

-- units have norm +- 1
-- norm x = x * conjugate x
-- norm (-x) = norm x

-- | The norm of a Dirichlet integer, obtained by multiplying it by its
-- 'conjugate'.  It satisfies
--
-- * @'norm' (x*y) = 'norm' x * 'norm' y@
--
-- * @'norm' ('inject' x) = x@
--
-- * @'norm' 'phi' = -1@
norm :: (Ring a) => Dirichlet a -> a
norm (D a b) = a*a + a*b - b*b
