{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Complex (Complex(..))
import Data.YAP.Polynomial (Polynomial)
import qualified Data.YAP.Polynomial as P
import Data.YAP.Polynomial.Z2 (PolynomialZ2)
import qualified Data.YAP.Polynomial.Z2 as PZ2
import Data.YAP.Quadratic.Eisenstein (Eisenstein(..))
import Data.YAP.Quadratic.Dirichlet (Dirichlet(..))

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

type DivisionCondition a = a -> a -> Bool

euclideanCondition :: (Eq a, Euclidean a) => DivisionCondition a
euclideanCondition a b =
    b == zero ||
    a == q*b + r && (r == zero || euclideanNorm r < euclideanNorm b)
  where
    (q, r) = divMod a b

instance (Arbitrary a) => Arbitrary (Eisenstein a) where
    arbitrary = I <$> arbitrary <*> arbitrary

instance (Arbitrary a) => Arbitrary (Dirichlet a) where
    arbitrary = D <$> arbitrary <*> arbitrary

instance (Arbitrary a) => Arbitrary (Polynomial a) where
    arbitrary = P.fromCoefficients <$> arbitrary

instance (Arbitrary a) => Arbitrary (PolynomialZ2 a) where
    arbitrary = PZ2.fromBits <$> arbitrary

main :: IO ()
main = defaultMainWithOpts
    [ testProperty "Complex numbers" $
        (euclideanCondition :: DivisionCondition (Complex Int))
    , testProperty "Eisenstein numbers" $
        (euclideanCondition :: DivisionCondition (Eisenstein Int))
    , testProperty "Dirichlet numbers" $
        (euclideanCondition :: DivisionCondition (Dirichlet Int))
    , testProperty "polynomials" $
        (euclideanCondition :: DivisionCondition (Polynomial Rational))
    , testProperty "polynomials (Z2)" $
        (euclideanCondition :: DivisionCondition (PolynomialZ2 Word))
    ] mempty
