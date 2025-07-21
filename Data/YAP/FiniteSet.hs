{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.FiniteSet
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: the semiring of finite sets.
--
-----------------------------------------------------------------------------

module Data.YAP.FiniteSet (
    -- * Finite sets
    FiniteSet,
    -- * Construction
    singleton,
    fromList,
    -- * Queries
    elems,
    -- * Finite formal languages
    FiniteLanguage,
    ) where

import Prelude.YAP
import Data.YAP.Algebra

import Data.Set (Set)
import qualified Data.Set as Set

-- | The semiring of sets over a monoid, with union as addition and the
-- monoid operation lifted to multiplication.
-- This is equivalent to 'Data.YAP.FiniteMap.FiniteMap' with a Boolean
-- semiring as codomain.
newtype FiniteSet a = FiniteSet (Set a)
    deriving (Eq, Ord)

instance (Show a) => Show (FiniteSet a) where
    showsPrec p x =
        showParen (p > 10) $ showString "fromList " . shows (elems x)

-- | A set containing a single element.
singleton :: a -> FiniteSet a
singleton s = FiniteSet (Set.singleton s)

-- | A set formed from a list by removing duplicates.
fromList :: Ord a => [a] -> FiniteSet a
fromList xs = FiniteSet (Set.fromList xs)

-- | The elements of the set.
elems :: FiniteSet a -> [a]
elems (FiniteSet s) = Set.elems s

-- | '(+)' is union
instance (Ord a) => AdditiveMonoid (FiniteSet a) where
    FiniteSet xs + FiniteSet ys = FiniteSet (Set.union xs ys)
    zero = FiniteSet Set.empty
    atimes = atimesIdempotent

-- | '(*)' is elementwise '<>'
instance (Ord a, Monoid a) => Semiring (FiniteSet a) where
    xs * ys = fromList [x <> y | x <- elems xs, y <- elems ys]
    one = singleton mempty

-- | Finite formal languages, with '(+)' as union and '(*)' as concatenation.
--
-- == __Examples__
--
-- >>> zero :: FiniteSet String
-- fromList []
-- >>> one :: FiniteSet String
-- fromList [""]
-- >>> (singleton "a" + singleton "ab") * (singleton "c" + singleton "bc")
-- fromList ["abbc","abc","ac"]
-- >>> (singleton "a" + singleton "ab")^3
-- fromList ["aaa","aaab","aaba","aabab","abaa","abaab","ababa","ababab"]
--
type FiniteLanguage a = FiniteSet [a]
