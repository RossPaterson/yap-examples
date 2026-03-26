{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Quadratic.Dirichlet

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

real :: Dirichlet Integer -> Double
real x = toReal (fmap fromInteger x)

compareProp :: Dirichlet Integer -> Dirichlet Integer -> Bool
compareProp x y =
    compare x y == compare (real x) (real y)

properFractionProp :: (OrderedRing a) => a -> Bool
properFractionProp x =
    x == fromInteger n + f && (f == 0 || compare f 0 == compare x 0) &&
    -1 < f && f < 1
  where
    (n, f) = properFraction x

floorProp :: Dirichlet Integer -> Bool
floorProp x =
    floor x == (floor (real x) :: Integer)

ceilingProp :: Dirichlet Integer -> Bool
ceilingProp x =
    ceiling x == (ceiling (real x) :: Integer)

roundProp :: Dirichlet Integer -> Bool
roundProp x =
    round x == (round (real x) :: Integer)

instance (Arbitrary a) => Arbitrary (Dirichlet a) where
    arbitrary = D <$> arbitrary <*> arbitrary

main :: IO ()
main = defaultMainWithOpts
    [ testProperty "compare" compareProp
    , testProperty "properFraction" $
        (properFractionProp :: Dirichlet Integer -> Bool)
    , testProperty "floor" floorProp
    , testProperty "ceiling" ceilingProp
    , testProperty "round" roundProp
    ] mempty
