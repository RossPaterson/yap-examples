{-# LANGUAGE RebindableSyntax #-}
module Data.YAP.Utilities.List where

import Prelude.YAP

longZipWith :: (a -> a -> a) -> [a] -> [a] -> [a]
longZipWith _ [] ys = ys
longZipWith _ xs [] = xs
longZipWith f (x:xs) (y:ys) = f x y:longZipWith f xs ys

mapOdds :: (a -> a) -> [a] -> [a]
mapOdds _ [] = []
mapOdds _ [x] = [x]
mapOdds f (x0:x1:xs) = x0:f x1:mapOdds f xs

-- balanced fold with an associative operation
foldb :: (a -> a -> a) -> a -> [a] -> a
foldb _ z [] = z
foldb _ _ [x] = x
foldb f z xs = f (foldb f z (odds xs)) (foldb f z (evens xs))

odds :: [a] -> [a]
odds [] = []
odds (x:xs) = x:evens xs

evens :: [a] -> [a]
evens [] = []
evens (_:xs) = odds xs

compose :: [a -> a] -> a -> a
compose = flip (foldr id)
