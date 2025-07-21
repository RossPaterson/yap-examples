{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Quaternion
-- Copyright   :  (c) Ross Paterson 2011
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: quaternions.
--
-----------------------------------------------------------------------------

module Data.YAP.Quaternion where

import Prelude.YAP
import Data.YAP.Algebra

-- | Quaternions
data Quaternion a = Q a a a a
    -- ^ @'Q' a b c d@ represents \(a + b i + c j + d k\).
    deriving (Eq, Ord, Show)

instance Functor Quaternion where
    fmap f (Q a b c d) = Q (f a) (f b) (f c) (f d)

instance (AdditiveMonoid a) => AdditiveMonoid (Quaternion a) where
    Q a1 b1 c1 d1 + Q a2 b2 c2 d2 = Q (a1+a2) (b1+b2) (c1+c2) (d1+d2)
    zero = Q zero zero zero zero
    atimes n = fmap (atimes n)

instance (AbelianGroup a) => AbelianGroup (Quaternion a) where
    negate = fmap negate
    gtimes n = fmap (gtimes n)

instance (Ring a) => Semiring (Quaternion a) where
    Q a1 b1 c1 d1 * Q a2 b2 c2 d2 = Q
        (a1*a2 - b1*b2 - c1*c2 - d1*d2)
        (a1*b2 + b1*a2 + c1*d2 - d1*c2)
        (a1*c2 - b1*d2 + c1*a2 + d1*b2)
        (a1*d2 + b1*c2 - c1*b2 + d1*a2)
    one = Q one zero zero zero
    fromNatural i = Q (fromNatural i) zero zero zero

instance (Ring a) => Ring (Quaternion a) where
    fromInteger i = Q (fromInteger i) zero zero zero

instance (FromRational a) => FromRational (Quaternion a) where
    fromRational x = Q (fromRational x) zero zero zero

instance (Field a) => DivisionSemiring (Quaternion a) where
    recip (Q a b c d) = Q (a/norm) (-b/norm) (-c/norm) (-d/norm)
      where
        norm = a*a + b*b + c*c + d*d

instance (Field a) => DivisionRing (Quaternion a)

-- | The conjugate of a quaternion.
conjugate :: (AbelianGroup a) => Quaternion a -> Quaternion a
conjugate (Q a b c d) = Q a (-b) (-c) (-d)
