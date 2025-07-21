{-# LANGUAGE RebindableSyntax #-}
module Data.YAP.Utilities.LinearEquations (LinearEqn, solveLinear) where

import Prelude.YAP
import Data.YAP.Algebra

import Data.List (partition)

-- | A linear equation of the form a1*x1 + ... + an*xn = b
type LinearEqn a = ([a], a)

minusLinearEqn :: (AbelianGroup a) => LinearEqn a -> LinearEqn a -> LinearEqn a
minusLinearEqn (as1, b1) (as2, b2) = (zipWith (-) as1 as2, b1 - b2)

scaleLinearEqn :: (Semiring a) => a -> LinearEqn a -> LinearEqn a
scaleLinearEqn c (as, b) = (map (c*) as, c*b)

-- the equation has a trivial unique solution
trivial :: (Eq a, AdditiveMonoid a) => LinearEqn a -> Bool
trivial (as, b) = null as && b == zero

-- | Find the unique solution to a system of linear equations, if one exists.
solveLinear :: (Eq a, Field a) => [LinearEqn a] -> Maybe [a]
solveLinear rs
  | all trivial rs = Just []
  | otherwise = -- Gaussian elimination
    case partition possiblePivot rs of
    (zeroes, pivot@(cp:lhsp, rhsp):rest) -> do
        -- solve for the rest of the variables, if possible
        values <- solveLinear (map reduce zeroes ++ map (eliminate pivot) rest)
        -- obtain value of the first variable by backward substitution
        let value = (rhsp - sum (zipWith (*) lhsp values)) / cp
        Just (value: values)
    _ -> Nothing

-- any row without a leading zero is a possible pivot
possiblePivot :: (Eq a, AdditiveMonoid a) => LinearEqn a -> Bool
possiblePivot ([], _) = error "possiblePivot []"
possiblePivot (a:_, _) = a == zero

-- Reduce an equation with a leading zero by deleting it
reduce :: LinearEqn a -> LinearEqn a
reduce ([], _) = error "reduce []"
reduce (_:lhs, rhs) = (lhs, rhs)

-- Eliminate the first variable from an equation by subtracting a
-- scaling of the pivot equation.
eliminate :: (Field a) => LinearEqn a -> LinearEqn a -> LinearEqn a
eliminate (cp:lhsp, rhsp) (c:lhs, rhs) =
    minusLinearEqn (lhs, rhs) (scaleLinearEqn (c/cp) (lhsp, rhsp))
eliminate _ _ = error "elimination with empty equations"
