{-# LANGUAGE RebindableSyntax #-}
module WeylAlgebraTests (tests) where

import Prelude.YAP
import qualified Data.YAP.Polynomial as P
import Data.YAP.DifferentialOperator

import Distribution.TestSuite

type Equation = (String, Weyl Integer, Weyl Integer)

equations :: [Equation]
equations = [
    ("D*x", d*x, x*d + 1),
    ("D^(3::Int)*x^(5::Int)", d^(3::Int) * x^(5::Int), x^(5::Int)*d^(3::Int) + 15*x^(4::Int)*d^(2::Int) + 60*x^(3::Int)*d + 60*x^(2::Int))]
  where
    d = diff
    x = multiply P.identity

equationTest :: Equation -> Test
equationTest (eq_name, xs, ys) = Test $ TestInstance {
    run = return $ Finished $ if xs == ys then Pass else Fail "not equal",
    name = eq_name,
    tags = [],
    options = [],
    setOption = \ _ _ -> Left "option not recognized"
    }

tests :: IO [Test]
tests = return (map equationTest equations)
