{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.DyadicRational

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

testProperty1 :: String -> (DyadicRational -> Bool) -> Test
testProperty1 = testProperty

testProperty2 :: String -> (DyadicRational -> DyadicRational -> Bool) -> Test
testProperty2 = testProperty

properFractionProp :: (OrderedRing a) => a -> Bool
properFractionProp x =
    x == fromInteger n + f && (f == 0 || compare f 0 == compare x 0) &&
    -1 < f && f < 1
  where
    (n, f) = properFraction x

instance Arbitrary DyadicRational where
    arbitrary = dyadic <$> arbitrary <*> arbitrary

main :: IO ()
main = defaultMainWithOpts
    [ testProperty2 "compare" $ \ x y ->
        compare x y == compare (toRational x) (toRational y)
    , testProperty2 "plus" $ \ x y ->
        toRational (x + y) == toRational x + toRational y
    , testProperty1 "negate" $ \ x ->
        toRational (negate x) == negate (toRational x)
    , testProperty2 "minus" $ \ x y ->
        toRational (x - y) == toRational x - toRational y
    , testProperty2 "multiply" $ \ x y ->
        toRational (x * y) == toRational x * toRational y
    , testProperty1 "properFraction" properFractionProp
    ] mempty
