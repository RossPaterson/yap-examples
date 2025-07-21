{-# LANGUAGE RebindableSyntax #-}
module PowerSeriesTests (tests) where

import Prelude.YAP
import qualified Data.YAP.PowerSeries as PS
import qualified Data.YAP.PowerSeries.Maclaurin as DS

import Distribution.TestSuite

type Equation f g = (String, f Rational, g Rational)

-- how far down the series to check for equality
depth :: Int
depth = 20

equation ::
    (f Rational -> [Rational]) -> (g Rational -> [Rational]) ->
    Equation f g -> Equation [] []
equation f g (eq_name, xs, ys) = (eq_name, f xs, g ys)

equations :: [Equation [] []]
equations =
    map (equation PS.coefficients DS.coefficients) [
        ("P=D recipOneMinus", PS.recipOneMinus, DS.recipOneMinus),
        ("P=D logOnePlus", PS.logOnePlus, DS.logOnePlus),
        ("P=D exp", PS.expS, DS.expS),
        -- trigonometric functions
        ("P=D sin", PS.sinS, DS.sinS),
        ("P=D cos", PS.cosS, DS.cosS),
        ("P=D tan", PS.tanS, DS.tanS),
        ("P=D sec", PS.secS, DS.secS),
        ("P=D asin", PS.asinS, DS.asinS),
        ("P=D atan", PS.atanS, DS.atanS),
        -- hyperbolic functions
        ("P=D sinh", PS.sinhS, DS.sinhS),
        ("P=D cosh", PS.coshS, DS.coshS),
        ("P=D tanh", PS.tanhS, DS.tanhS),
        ("P=D sech", PS.sechS, DS.sechS),
        ("P=D asinh", PS.asinhS, DS.asinhS),
        ("P=D atanh", PS.atanhS, DS.atanhS)] ++
    map (equation PS.coefficients PS.coefficients) [
        ("P compose exp log", PS.compose PS.expS PS.logOnePlus, 1 + PS.identity),
        ("P compose log exp", PS.compose PS.logOnePlus (PS.expS - 1), PS.identity),
        -- trigonometric functions
        ("P sin^2 + cos^2 = 1", PS.sinS^(2::Int) + PS.cosS^(2::Int), 1),
        ("P cos * sec = 1", PS.cosS * PS.secS, 1),
        ("P sin * sec = tan", PS.sinS * PS.secS, PS.tanS),
        ("P compose sin asin", PS.compose PS.sinS PS.asinS, PS.identity),
        ("P compose tan atan", PS.compose PS.tanS PS.atanS, PS.identity),
        ("P inverse sin asin", PS.inverse PS.sinS, PS.asinS),
        ("P inverse tan atan", PS.inverse PS.tanS, PS.atanS),
        -- hyperbolic functions
        ("P cosh^2 - sinh^2 = 1", PS.coshS^(2::Int) - PS.sinhS^(2::Int), 1),
        ("P cosh * sech = 1", PS.coshS * PS.sechS, 1),
        ("P sinh * sech = tanh", PS.sinhS * PS.sechS, PS.tanhS),
        ("P compose sinh asinh", PS.compose PS.sinhS PS.asinhS, PS.identity),
        ("P compose tanh atanh", PS.compose PS.tanhS PS.atanhS, PS.identity),
        ("P inverse sinh asinh", PS.inverse PS.sinhS, PS.asinhS),
        ("P inverse tanh atanh", PS.inverse PS.tanhS, PS.atanhS)] ++
    map (equation DS.coefficients DS.coefficients) [
        ("D compose exp log", DS.compose DS.expS DS.logOnePlus, 1 + DS.identity),
        ("D compose log exp", DS.compose DS.logOnePlus (DS.expS - 1), DS.identity),
        ("D tree", DS.inverseSimple (DS.mulX (DS.expS DS..* (-1))), DS.tree),
        ("D lambertW", DS.inverseSimple (DS.mulX DS.expS), DS.lambertW),
        -- trigonometric functions
        ("D sin^2 + cos^2 = 1", DS.sinS^(2::Int) + DS.cosS^(2::Int), 1),
        ("D cos * sec = 1", DS.cosS * DS.secS, 1),
        ("D sin * sec = tan", DS.sinS * DS.secS, DS.tanS),
        ("D compose sin asin", DS.compose DS.sinS DS.asinS, DS.identity),
        ("D compose tan atan", DS.compose DS.tanS DS.atanS, DS.identity),
        ("D inverse sin asin", DS.inverse DS.sinS, DS.asinS),
        ("D inverse tan atan", DS.inverse DS.tanS, DS.atanS),
        -- hyperbolic functions
        ("D cosh^2 - sinh^2 = 1", DS.coshS^(2::Int) - DS.sinhS^(2::Int), 1),
        ("D cosh * sech = 1", DS.coshS * DS.sechS, 1),
        ("D sinh * sech = tanh", DS.sinhS * DS.sechS, DS.tanhS),
        ("D compose sinh asinh", DS.compose DS.sinhS DS.asinhS, DS.identity),
        ("D compose tanh atanh", DS.compose DS.tanhS DS.atanhS, DS.identity),
        ("D inverse sinh asinh", DS.inverse DS.sinhS, DS.asinhS),
        ("D inverse tanh atanh", DS.inverse DS.tanhS, DS.atanhS)]

equationTest :: Equation [] [] -> Test
equationTest (eq_name, xs, ys) = Test $ TestInstance {
    run = return $ Finished $
        if take depth xs == take depth ys then Pass else Fail "not equal",
    name = eq_name,
    tags = [],
    options = [],
    setOption = \ _ _ -> Left "option not recognized"
    }

tests :: IO [Test]
tests = return (map equationTest equations)
