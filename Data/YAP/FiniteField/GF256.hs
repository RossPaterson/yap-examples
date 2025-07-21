{-# LANGUAGE RebindableSyntax #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.YAP.FiniteField.GF256
-- Copyright   :  (c) Ross Paterson 2021
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- An example instance of the algebraic classes: the finite field (or Galois
-- field) of order \(256 = 2^8\).
--
-- In general, finite fields have order \(p^k\), where \(p\) is prime and
-- \(k > 0\).  All the fields of a given order are isomorphic.  They may
-- be constructed as quotients \({\Bbb Z}_p[X]/\langle P \rangle\), where
-- \(P\) is an irreducible polynomial of degree \(k\) over \({\Bbb Z}_p\).
--
-- This version uses the Conway polynomial, \(x^8 + x^4 + x^3 + x^2 + 1\),
-- as used in QR codes.  Other applications use different codings,
-- derived from different polynomials.
--
-----------------------------------------------------------------------------

module Data.YAP.FiniteField.GF256 (GF256, gf256, generator, fromGF256) where

import Prelude.YAP
import Data.YAP.Algebra
import Data.YAP.Polynomial.Z2

{-
A field of order p^k can be constructed as the quotient Z_p[x]/<q>,
where q is an irreducible polynomial of degree k in Z_p[x].  If this
polynomial is primitive (which implies that it is irreducible), then
its root is a generator for the resulting field.

The coding of the field varies with the choice of quotient polynomial,
though all resulting fields of p^k elements are isomorphic.  The Conway
polynomials define a canonical choice of primitive polynomial for each
p and k.  For p = 2 and k = 8, this is

    x^8 + x^4 + x^3 + x^2 + 1

This is used in QR codes.
Data Matrix and Aztec codes use x^8 + x^5 + x^3 + x^2 + 1 (primitive).
Rijndael/AES uses x^8 + x^4 + x^3 + x + 1 (irreducible but not primitive).
-}
modulus :: PolynomialZ2 Int
modulus = fromIndices [8, 4, 3, 2, 0]

-- | Finite field of order 256, with elements represented as eight bits.
newtype GF256 = GF256 (PolynomialZ2 Int)
    deriving (Eq)

-- | Construct an element of the field coded using the low-order 8 bits
-- of @n@.  This function is different from 'fromInteger', which maps
-- everything to @0@ or @1@.  'gf256' preserves @0@ and @1@, but does
-- not preserve the arithmetic operators.
gf256 :: Int -> GF256
gf256 n = GF256 (fromBits (n `mod` 256))

-- | A standard generator of the field: @'gf256' 2@ (which is not the
-- same as @2::'GF256' = 'fromInteger' 2 = 0@).  The expression
--
-- >>> iterate (* generator) 1
-- [gf256 1,gf256 2,gf256 4,gf256 8,gf256 16,gf256 32,gf256 64,gf256 128,
--  gf256 29,gf256 58,gf256 116,gf256 232,gf256 205,gf256 135,gf256 19,...
--
-- repeats after 255 steps, having gone through all the non-zero elements
-- of the field (in a non-obvious order).
generator :: GF256
generator = gf256 2

-- | The representation of an element of the field as a number between @0@
-- and @255@.
fromGF256 :: GF256 -> Int
fromGF256 (GF256 x) = bits x

instance Show GF256 where
    showsPrec p (GF256 n) =
        showParen (p > 10) $ showString "gf256 " . shows (bits n)

instance AdditiveMonoid GF256 where
    GF256 x + GF256 y = GF256 (x + y)
    zero = GF256 zero
    atimes n (GF256 x) = GF256 (atimes n x)

instance AbelianGroup GF256 where
    negate = id
    gtimes n (GF256 x) = GF256 (gtimes n x)

-- | @'fromNatural' n@ is @0@ if @n@ is even and @1@ if it is odd.
instance Semiring GF256 where
    GF256 x * GF256 y = GF256 (x*y `mod` modulus)
    one = GF256 one

-- | @'fromInteger' n@ is @0@ if @n@ is even and @1@ if it is odd.
instance Ring GF256 where

instance DivisionSemiring GF256 where
    recip (GF256 x) = GF256 (fst (bezout x modulus))

instance Semifield GF256

instance DivisionRing GF256

instance Field GF256
