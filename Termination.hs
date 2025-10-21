{-@ LIQUID "--reflection" @-}
module Termination where

import Prelude hiding (gcd)
import BasicsSol hiding (append)
import Language.Haskell.Liquid.ProofCombinators

{-@ lazy wrongFactorial @-}
{-@ wrongFactorial :: Nat -> Nat @-}
wrongFactorial :: Int -> Int
wrongFactorial 0 = 1
wrongFactorial n = n * wrongFactorial n


-- data List a = Nil | Cons a (List a)

append :: List a -> List a -> List a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)


--------------------------------------------------------------------------------
-- Theorem 1. Let n ∈ Z be an integer. Then, n = 0.
-- Proof: Take n to be any integer. By Theorem 1, we can conclude that n is
-- indeed equal to 0. QED.
--------------------------------------------------------------------------------

-- Ackermann function
{-@ lazy ack @-}
{-@ ack :: m:Nat -> n:Nat -> Nat @-}
ack :: Int -> Int -> Int
ack 0 n = n + 1
ack m 0 = ack (m-1) 1
ack m n = ack (m-1) (ack m (n-1))


--------------------------------------------------------------------------------
-- EXERCISE: Why does the follow implementation of the greatest common divisor
-- terminate? Find a termination measure.
{-@ lazy gcd @-}
{-@ gcd :: a:Nat -> b:Nat -> Int @-}
gcd :: Int -> Int -> Int
gcd 0 b = 0
gcd a 0 = a
gcd a b | a == b = a
        | a >  b = gcd (a - b) b
        | a <  b = gcd a (b - a)
--------------------------------------------------------------------------------


-- mutual recursion!

{-@ lazy isEven @-}
{-@ isEven :: n:Nat -> Bool @-}
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n-1)

{-@ lazy isOdd @-}
{-@ isOdd :: n:Nat -> Bool @-}
isOdd :: Int -> Bool
isOdd n = not (isEven n)
