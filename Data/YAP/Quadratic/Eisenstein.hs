{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Quadratic.Eisenstein
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: Eisenstein integers.
-- (a complex quadratic integer ring).
--
-----------------------------------------------------------------------------

module Data.YAP.Quadratic.Eisenstein (
    Eisenstein(..),
    primitive, sextant,
    -- * Complex number operations
    real, conjugate, toComplex,
    -- * Triangular lattice
    distance,
    ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Complex (Complex(..))

-- | @I a b@ represents \(a + b\omega\), where
-- \(\omega = {-1 + i\sqrt 3 \over 2}\) (the primitive third root of unity).
-- When \(a\) and \(b\) are integers, this ring \({\Bbb Z}(\omega)\) is
-- equivalent to the ring of algebraic integers of the complex quadratic
-- field \({\Bbb Q}(\sqrt{-3})\).
--
-- <<images/Eisenstein_integer_grid.svg>>
-- (image from Wikimedia Commons)
--
-- These are useful as coordinates in a triangular lattice, or equivalently
-- a hexagonal tiling.
data Eisenstein a = I a a
    deriving (Eq, Show)

instance Functor Eisenstein where
    fmap f (I a b) = I (f a) (f b)

instance (AdditiveMonoid a) => AdditiveMonoid (Eisenstein a) where
    I a b + I c d = I (a+c) (b+d)
    zero = real zero
    atimes n (I a b) = I (atimes n a) (atimes n b)

instance (AbelianGroup a) => AbelianGroup (Eisenstein a) where
    negate (I a b) = I (negate a) (negate b)
    gtimes n (I a b) = I (gtimes n a) (gtimes n b)

instance (Ring a) => Semiring (Eisenstein a) where
    I a b * I c d = I (a*c - b*d) (a*d + b*c - b*d)
    one = real one
    fromNatural a = real (fromNatural a)

instance (Ring a) => Ring (Eisenstein a) where
    fromInteger a = real (fromInteger a)

instance (FromRational a) => FromRational (Eisenstein a) where
    fromRational a = real (fromRational a)

-- | The norm is the squared magnitude of the complex number.
instance (Ring a, ToInteger a) => Euclidean (Eisenstein a) where
    I ax bx `div` y@(I ay by) = I a b
      where
        -- x / y = h/(2*d) + sqrt 3/(2*d)*k*i
        --       = (h + k)/(2*d) + k/d*w
        d = norm y
        -- real part of exact division, multiplied by 2*d
        h = 2*ax*ay - bx*ay - ax*by + 2*bx*by
        -- imaginary part of exact division, multiplied by 2/sqrt 3*d
        k = bx*ay - ax*by
        a = round_div_int (h + k) (2*d)
        b = round_div_int k d
        round_div_int i n = (2*i + n) `div` (2*n)
    x `mod` y = x - y*(x `div` y)
    divMod x y = (q, x - y*q)
      where q = x `div` y

    euclideanNorm x = euclideanNorm (toInteger (norm x))

norm :: (Ring a) => Eisenstein a -> a
norm (I a b) = a*a - a*b + b*b

-- | @'stdUnit' x@ has norm one.
-- If @x@ is non-zero, @'stdAssociate' x@ has the form @I a b@ where
-- @0 <= b < a@. There are 6 units, the powers of 'primitive'.
instance (Ring a, ToInteger a) => StandardAssociate (Eisenstein a) where
    stdUnit x = primitive ^ sextant x
    stdRecip x = primitive ^ ((- sextant x) `mod` 6)

instance (Field a) => DivisionSemiring (Eisenstein a) where
    recip x = fmap (/ norm x) (conjugate x)

instance (Field a) => Semifield (Eisenstein a)

instance (Field a) => DivisionRing (Eisenstein a) where

instance (Field a) => Field (Eisenstein a)

-- | Inject a real number
real :: (AdditiveMonoid a) => a -> Eisenstein a
real a = I a zero

-- | primitive 6th root of unity, \(1+\omega = {1 + i\sqrt 3 \over 2}\)
primitive :: Semiring a => Eisenstein a
primitive = I one one

-- | The sextant of the plane containing the value, counting
-- counterclockwise from the positive real line.  Zero is assigned to
-- sextant 0.
sextant :: (Ring a, Ord a) => Eisenstein a -> Int
sextant (I a b)
  | b >= a && a > 0 = 1
  | a <= 0 && -b < a = 2
  | a < b && b <= 0 = 3
  | b <= a && a < 0 = 4
  | -b > a && a >= 0 = 5
  | otherwise = 0

-- | Convert to a complex number
toComplex :: (Floating a) => Eisenstein a -> Complex a
toComplex (I a b) = (a-b)/2 :+ sqrt 3/2*b

-- | Complex conjugate, satisfying
--
-- * @'conjugate' ('conjugate' x) = x@
--
-- * @'conjugate' ('real' n) = 'real' n@
--
conjugate :: (AbelianGroup a) => Eisenstein a -> Eisenstein a
conjugate (I a b) = I (a-b) (negate b)

-- | Distance in the triangular lattice
distance :: (Ord a, AbelianGroup a, StandardAssociate a) => Eisenstein a -> a
distance (I a b) = maximum [stdUnit a, stdUnit b, stdUnit (a-b)]
