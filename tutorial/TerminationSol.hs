{-@ LIQUID "--reflection" @-}
module TerminationSol where

import Prelude hiding (gcd)
import BasicsSol hiding (append)
import Language.Haskell.Liquid.ProofCombinators

-- {-@ wrongFactorial :: Nat -> Nat @-}
-- wrongFactorial :: Int -> Int
-- wrongFactorial 0 = 1
-- wrongFactorial n = n * wrongFactorial n

{-@ factorial :: Nat -> Nat @-}
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n-1)

{-@ range :: a:Int -> b:{Int | b >= a} -> List {n:Int | a <= n && n < b}
           / [b-a] @-}
range :: Int -> Int -> List Int
range a b = if a == b then Nil else Cons a (range (a+1) b)


-- data List a = Nil | Cons a (List a)

append :: List a -> List a -> List a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)


{-@ lazy nIsZero @-}
{-@ nIsZero :: n:Int -> { n == 0 } @-}
nIsZero :: Int -> Proof
nIsZero n = nIsZero n

-- Ackermann function
{-@ lazy ack @-}
{-@ ack :: m:Nat -> n:Nat -> Nat / [m,n] @-}
ack :: Int -> Int -> Int
ack 0 n = n + 1
ack m 0 = ack (m-1) 1
ack m n = ack (m-1) (ack m (n-1))

--------------------------------------------------------------------------------
-- EXERCISE: Why does the follow implementation of the greatest common divisor
-- terminate? Find a termination measure.
{-@ lazy gcd @-}
{-@ gcd :: a:Nat -> b:Nat -> Int / [a,b] @-}
gcd :: Int -> Int -> Int
gcd 0 b = 0
gcd a 0 = a
gcd a b | a == b = a
        | a >  b = gcd (a - b) b
        | a <  b = gcd a (b - a)
--------------------------------------------------------------------------------

-- mutual recursion!

{-@ isEven :: n:Nat -> Bool / [n, 1] @-}
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n-1)

{-@ isOdd :: n:Nat -> Bool / [n, 2] @-}
isOdd :: Int -> Bool
isOdd n = not (isEven n)
