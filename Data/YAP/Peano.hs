{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.Peano
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: lazy Peano numerals.
--
-----------------------------------------------------------------------------
module Data.YAP.Peano (Peano(..), peano, maybeMinus) where

import Prelude.YAP
import Data.YAP.Algebra

-- | Lazy Peano numerals: a unary representation of the natural numbers,
-- which is very inefficient, but does offer lazy semantics.
data Peano = Zero | Succ Peano
    deriving (Eq, Ord, Read, Show)

-- | '(+)' is lazy in the second argument
instance AdditiveMonoid Peano where
    zero = Zero
    x + y = peano y Succ x
    atimes n x = times (toInteger n) (x+) Zero

instance Semiring Peano where
    x * y = peano Zero (y+) x
    one = Succ Zero
    fromNatural i = times (toInteger i) Succ Zero

-- | Eliminator for Peano numerals: @'peano' z s@ replaces 'Zero' with @z@
-- and 'Succ' with @s@.
peano :: a -> (a -> a) -> Peano -> a
peano z _ Zero = z
peano z s (Succ x) = s (peano z s x)

times :: Integer -> (a -> a) -> a -> a
times n f x
  | n <= 0 = x
  | otherwise = f (times (n-1) f x)

-- | The only unit is 'one'. 'stdAssociate' is the identity.
instance StandardAssociate Peano where
    stdAssociate x = x
    stdUnit _ = one
    stdRecip _ = one

instance Euclidean Peano where
    divMod x y
      | y == zero = error "division by zero"
      | otherwise = divModAux x
      where
        divModAux z = case maybeMinus z y of
            Nothing -> (Zero, z)
            Just z' -> let (q, r) = divModAux z' in (Succ q, r)

    euclideanNorm = peano zero (+one)

-- | Partial subtraction
maybeMinus :: Peano -> Peano -> Maybe Peano
maybeMinus x Zero = Just x
maybeMinus Zero (Succ _) = Nothing
maybeMinus (Succ x) (Succ y) = maybeMinus x y

instance ToRational Peano where
    toRational x = toRational (toInteger x)

instance ToInteger Peano where
    toInteger = peano 0 (+1)
