module BasicsSol where

import Prelude hiding (length, take, drop, map, lookup)

{-@ abs :: Int -> {v:Int | v >= 0} @-}
abs :: Int -> Int
abs x = undefined

percentage :: Int -> Int -> Int
percentage total part = (part * 100) `div` total

-- {-@ percentage :: {total:Int | total /= 0} -> Int -> Int @-}

-- {-@ percentage :: {total:Int | total => 0} -> {part:Int | part <= total && part >= 0}
--                -> Int @-}

-- {-@ percentage :: {total:Int | total => 0} -> {part:Int | part <= total && part >= 0}
--                -> {r:Int | r >= 0 && r <= 100} @-}

{-@ type Positive     = {v:Int | v >  0} @-}
{-@ type NonNegative  = {v:Int | v >= 0} @-}
{-@ type NonZero      = {v:Int | v /= 0} @-}
{-@ type Between L U  = {v:Int | L <= v && v < U} @-}

{-@ percentage :: total:Positive -> part:Between 0 total -> Between 0 101 @-}

data List a = Nil | Cons a (List a)
  deriving (Show, Eq, Ord)

{-@ length :: List a -> Nat @-}
length :: List a -> Int
length Nil         = 0
length (Cons _ xs) = 1 + length xs

{-@ measure length @-}

{-@ head :: {xs:List a | length xs > 0} -> a @-}
head :: List a -> a
head (Cons x _) = x

{-@ take :: n:Nat -> {xs:List a | length xs >= n}
         -> {ys:List a | length ys == n} @-}
take :: Int -> List a -> List a
take 0 _           = Nil
take n (Cons x xs) = Cons x (take (n - 1) xs)

{-@ drop :: n:Nat -> {xs:List a | length xs >= n}
         -> {ys:List a | length ys == length xs - n} @-}
drop :: Int -> List a -> List a
drop 0 xs          = xs
drop n (Cons _ xs) = drop (n - 1) xs

{-@ lookup :: i:Nat -> {xs:List a | length xs > i} -> a @-}
lookup :: Int -> List a -> a
lookup 0 (Cons x _)  = x
lookup n (Cons _ xs) = lookup (n - 1) xs

{-@ append :: xs:List a -> ys:List a
           -> {zs:List a | length zs == length xs + length ys} @-}
append :: List a -> List a -> List a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@ insertAt :: n:Nat -> a -> {l:List a | length l >= n} -> List a @-}
insertAt :: Int -> a -> List a -> List a
insertAt 0 x ys = Cons x ys
insertAt n x (Cons y ys) = Cons y (insertAt (n-1) x ys)

{-@ map :: (a -> b) -> xs:List a -> {ys:List b | length ys == length xs} @-}
map :: (a -> b) -> List a -> List b
map _ Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)
