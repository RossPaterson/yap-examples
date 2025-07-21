{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
module CliffordInverseProof (tests) where

-- Symbolic proof of inversion formulas for Clifford algebras p+q <= 5.

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.CliffordAlgebra
import Data.YAP.FiniteMap

import Distribution.TestSuite
import Data.List (subsequences)
import GHC.TypeLits

-- Multivectors with variable coefficients

type GenMultivector p q = Multivector p q 0 (GenPolynomial Xs Int)
type Inverter p q = GenMultivector p q -> GenMultivector p q

-- general multivector with a distinct variable for each combination
-- drawn from p positive basis vectors and q negative basis vectors
genMV :: (KnownNat p, KnownNat q) => GenMultivector p q
genMV = genMVAux natSing natSing

genMVAux :: (KnownNat p, KnownNat q) => SNat p -> SNat q -> GenMultivector p q
genMVAux sing_p sing_q =
    sum [scalar (genIndeterminate (X k)) * product [basic i | i <- is] |
        (k, is) <- zip (iterate (+one) one) (subsequences [0..p+q-1])]
  where
    p = intVal sing_p
    q = intVal sing_q

intVal :: (KnownNat n) => SNat n -> Int
intVal n = fromInteger (natVal n)

-- Check that v * f v is a scalar for general v
validInverter :: (KnownNat p, KnownNat q) => Inverter p q -> Bool
validInverter inv = map fst (toBlades (v * inv v)) == [[]]
  where
    v = genMV

testInverter :: (KnownNat p, KnownNat q) => Inverter p q -> Test
testInverter inv = Test $ TestInstance {
    run = return $ Finished $
        if validInverter inv then Pass else Fail "not scalar",
    name = "signature " ++ show sig,
    tags = [],
    options = [],
    setOption = \ _ _ -> Left "option not recognized"
    }
  where
    sig = inverterSignature inv natSing natSing

inverterSignature :: (KnownNat p, KnownNat q) =>
    Inverter p q -> SNat p -> SNat q -> (Int, Int)
inverterSignature _ sing_p sing_q = (p, q)
  where
    p = intVal sing_p
    q = intVal sing_q

-- suitable functions for n = 3..5

conjugate3 :: (KnownNat p, KnownNat q, KnownNat r, Eq a, Ring a) =>
    Multivector p q r a -> Multivector p q r a
conjugate3 v = conjugate v * gradeInvolution v * reversion v

conjugate4 :: (KnownNat p, KnownNat q, KnownNat r, Eq a, Ring a) =>
    Multivector p q r a -> Multivector p q r a
conjugate4 v = c1 * involution (\ n -> n >= 3) (v * c1)
  where
    c1 = conjugate v

conjugate5 :: (KnownNat p, KnownNat q, KnownNat r, Eq a, Ring a) =>
    Multivector p q r a -> Multivector p q r a
conjugate5 v = c3 * involution (\ n -> n `mod` 3 == 1) (v * c3)
  where
    c3 = conjugate3 v

tests :: IO [Test]
tests = return [
    testInverter (conjugate :: Inverter 1 0),
    testInverter (conjugate :: Inverter 0 1),
    testInverter (conjugate :: Inverter 2 0),
    testInverter (conjugate :: Inverter 1 1),
    testInverter (conjugate :: Inverter 0 2),
    testInverter (conjugate3 :: Inverter 3 0),
    testInverter (conjugate3 :: Inverter 2 1),
    testInverter (conjugate3 :: Inverter 1 2),
    testInverter (conjugate3 :: Inverter 0 3),
    testInverter (conjugate4 :: Inverter 4 0),
    testInverter (conjugate4 :: Inverter 3 1),
    testInverter (conjugate4 :: Inverter 2 2),
    testInverter (conjugate4 :: Inverter 1 3),
    testInverter (conjugate4 :: Inverter 0 4)
    -- these are too memory-hungry
    -- testInverter (conjugate5 :: Inverter 5 0),
    -- testInverter (conjugate5 :: Inverter 4 1),
    -- testInverter (conjugate5 :: Inverter 3 2),
    -- testInverter (conjugate5 :: Inverter 2 3),
    -- testInverter (conjugate5 :: Inverter 1 4),
    -- testInverter (conjugate5 :: Inverter 0 5)
    ]
