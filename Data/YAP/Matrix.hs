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
-- An example instance of the algebraic classes: matrices.
--
-----------------------------------------------------------------------------

module Data.YAP.Matrix (
    Matrix, matrix, rows, multiply, transpose, apply,
    ) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Vector

import qualified Data.List as List
import GHC.TypeLits

-- | Matrix with @m@ rows and @n@ columns
newtype Matrix (m::Nat) (n::Nat) a = Matrix [[a]]
    deriving (Eq, Ord)

-- Construct a matrix from a list of m lists of length n.
makeMatrix :: (KnownNat m, KnownNat n) =>
    (Int -> Int -> [[a]]) -> Matrix m n a
makeMatrix k = makeMatrixSing $ \ m n -> Matrix (k (intVal m) (intVal n))

-- helper to provide singletons for m and n
makeMatrixSing :: (KnownNat m, KnownNat n) =>
    (SNat m -> SNat n -> Matrix m n a) -> Matrix m n a
makeMatrixSing k = k natSing natSing

intVal :: (KnownNat n) => SNat n -> Int
intVal = fromInteger . natVal

instance (Show a) => Show (Matrix m n a) where
    showsPrec p (Matrix xss) =
        showParen (p > 10) $ showString "matrix " . shows xss

instance Functor (Matrix m n) where
    fmap f (Matrix xss) = Matrix (map (map f) xss)

instance (KnownNat m, KnownNat n) => Applicative (Matrix m n) where
    pure x = makeMatrix $ \ m n -> replicate m (replicate n x)
    Matrix fss <*> Matrix xss = Matrix (zipWith (zipWith ($)) fss xss)

instance (KnownNat m, KnownNat n, AdditiveMonoid a) =>
        AdditiveMonoid (Matrix m n a) where
    xss + yss = (+) <$> xss <*> yss
    zero = pure zero
    atimes n = fmap (atimes n)

instance (KnownNat m, KnownNat n, AbelianGroup a) =>
        AbelianGroup (Matrix m n a) where
    xss - yss = (-) <$> xss <*> yss
    negate = fmap negate
    gtimes n = fmap (gtimes n)

-- | Construct a matrix from a list of row values.
matrix :: (KnownNat m, KnownNat n, AdditiveMonoid a) => [[a]] -> Matrix m n a
matrix xss = makeMatrix $ \ m n ->
    take m ([take n (xs ++ repeat zero) | xs <- xss] ++
        repeat (replicate n zero))

-- | The rows of a matrix
rows :: Matrix m n a -> [[a]]
rows (Matrix xss) = xss

-- | Transpose of a matrix
transpose :: (KnownNat m, KnownNat n) => Matrix m n a -> Matrix n m a
transpose (Matrix xss) = Matrix (List.transpose xss)

-- | Multiply a vector by a matrix.
apply :: (Semiring a) => Matrix m n a -> Vector n a -> Vector m a
apply (Matrix xss) v =
    unsafeVector (map (flip dot_product (coordinates v)) xss)

dot_product :: (Semiring a) => [a] -> [a] -> a
dot_product xs ys = sum (zipWith (*) xs ys)

-- | Multiply matrices
multiply :: (KnownNat p, Semiring a) =>
    Matrix m n a -> Matrix n p a -> Matrix m p a
multiply (Matrix xss) (Matrix yss) =
    Matrix [[dot_product xs ys | ys <- yss_t] | xs <- xss]
  where
    yss_t = List.transpose yss
