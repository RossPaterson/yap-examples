{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds, KindSignatures #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Matrix
-- Copyright   :  (c) Ross Paterson 2023
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  type-level literals
--
-- An example instance of the algebraic classes: square matrices.
--
-----------------------------------------------------------------------------

module Data.YAP.Matrix.Square (
    Matrix(..), matrix,
    diagonal, transpose, determinant, adjugate,
    apply,
    characteristicPolynomial,
    ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Vector
import qualified Data.YAP.Matrix as Gen
import qualified Data.YAP.Polynomial as Poly
import Data.YAP.Polynomial (Polynomial)

import GHC.TypeLits
import qualified Data.List as List

-- | Square @n@x@n@ matrices
newtype Matrix n a = Square (Gen.Matrix n n a)
    deriving (Eq, Ord)

instance (Show a) => Show (Matrix n a) where
    showsPrec p m =
        showParen (p > 10) $ showString "matrix " . shows (rows m)

size :: (KnownNat n) => Matrix n a -> Int
size m = intVal (natVal1 m)

intVal :: (KnownNat n) => SNat n -> Int
intVal = fromInteger . natVal

natVal1 :: (KnownNat n) => proxy n a -> SNat n
natVal1 _ = natSing

rows :: Matrix n a -> [[a]]
rows (Square m) = Gen.rows m

instance Functor (Matrix n) where
    fmap f (Square xss) = Square (fmap f xss)

instance (KnownNat n) => Applicative (Matrix n) where
    pure x = Square (pure x)
    Square fss <*> Square xss = Square (fss <*> xss)

instance (KnownNat n, AdditiveMonoid a) => AdditiveMonoid (Matrix n a) where
    Square xss + Square yss = Square (xss + yss)
    zero = Square zero
    atimes n = fmap (atimes n)

instance (KnownNat n, AbelianGroup a) => AbelianGroup (Matrix n a) where
    Square xss - Square yss = Square (xss - yss)
    negate = fmap negate
    gtimes n = fmap (gtimes n)

instance (KnownNat n, Semiring a) => Semiring (Matrix n a) where
    Square xss * Square yss = Square (Gen.multiply xss yss)
    one = diagonal one
    fromNatural x = diagonal (fromNatural x)

instance (KnownNat n, Ring a) => Ring (Matrix n a) where
    fromInteger x = diagonal (fromInteger x)

instance (KnownNat n, FromRational a) => FromRational (Matrix n a) where
    fromRational x = diagonal (fromRational x)

-- | Construct a square matrix from a list of row values.
matrix :: (KnownNat n, AdditiveMonoid a) => [[a]] -> Matrix n a
matrix xss = Square (Gen.matrix xss)

-- | Square matrix with @x@'s along the diagonal
diagonal :: (KnownNat n, AdditiveMonoid a) => a -> Matrix n a
diagonal x = matrix $ iterate (zero:) (x:repeat zero)

-- | Transpose of a square matrix
transpose :: (KnownNat n) => Matrix n a -> Matrix n a
transpose (Square m) = Square (Gen.transpose m)

-- | Determinant of a square matrix
determinant :: (KnownNat n, Ring a) => Matrix n a -> a
determinant m = det (size m) (rows m)

det :: (Ring a) => Int -> [[a]] -> a
det n xss
  | n == 0 = one
  | otherwise =
    sum (zipWith (*) (iterate negate one)
       (zipWith (*) (map head xss)
           (map (det (n-1)) (dropOne (map tail xss)))))

-- | Adjugate of a square matrix, satisfying
--
-- @
-- m * 'adjugate' m = 'diagonal' ('determinant' m)
-- @
--
-- /Caution:/ The implementation used here is very inefficient, and also
-- not a numerically stable method for matrix inversion.
adjugate :: (KnownNat n, Ring a) => Matrix n a -> Matrix n a
adjugate m = matrix (adj (size m) (rows m))

adj :: (Ring a) => Int -> [[a]] -> [[a]]
adj n xss
  | n == 0 = []
  | otherwise =
    List.transpose $
        zipWith flipSigns (iterate negate one) $
        map (map (det (n-1)) . List.transpose . map dropOne) $
        dropOne xss

flipSigns :: (Ring a) => a -> [a] -> [a]
flipSigns s = zipWith (*) (iterate negate s)

-- ways of dropping one element from a list
dropOne :: [a] -> [[a]]
dropOne [] = []
dropOne (x:xs) = xs:map (x:) (dropOne xs)

-- | Multiply a vector by a square matrix.
apply :: (Semiring a) => Matrix n a -> Vector n a -> Vector n a
apply (Square m) v = Gen.apply m v

-- | The characteristic polynomial of a square matrix, \(det(x I - A)\),
-- a monic polynomial of degree \(n\) whose roots are the eigenvalues of \(A\).
characteristicPolynomial :: (KnownNat n, Ring a) => Matrix n a -> Polynomial a
characteristicPolynomial m =
    determinant (diagonal Poly.identity - fmap Poly.constant m)
