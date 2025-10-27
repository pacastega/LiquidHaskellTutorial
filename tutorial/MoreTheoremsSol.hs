{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module MoreTheoremsSol where

import Prelude hiding (lookup,length,take,drop)
import BasicsSol hiding (take,drop)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect take @-}
{-@ take :: n:Nat -> {xs:List a | length xs >= n}
         -> {ys:List a | length ys == n} @-}
take :: Int -> List a -> List a
take 0 _           = Nil
take n (Cons x xs) = Cons x (take (n - 1) xs)

{-@ reflect drop @-}
{-@ drop :: n:Nat -> {xs:List a | length xs >= n}
         -> {ys:List a | length ys == length xs - n} @-}
drop :: Int -> List a -> List a
drop 0 xs          = xs
drop n (Cons _ xs) = drop (n - 1) xs

{-@ reflect rotate @-}
{-@ rotate :: xs:List a -> n:Between 0 (length xs) -> List a @-}
rotate :: List a -> Int -> List a
rotate xs n = append (drop n xs) (take n xs)

{-@ rotateCorrect :: xs:List a -> n:Between 0 (length xs)
                  -> i:Between 0 (length xs)
                  -> {lookup i (rotate xs n) = lookup ((i+n) mod (length xs)) xs}
@-}
rotateCorrect :: Eq a => List a -> Int -> Int -> Proof
rotateCorrect xs n i = let ys = take n xs; zs = drop n xs in
  if i < length xs - n
  then lookupAppendLeft zs ys i ? takeDropAppend xs n ? lookupAppendRight ys zs i
  else lookupAppendRight zs ys i' ? takeDropAppend xs n ? lookupAppendLeft ys zs i'
    where i' = i + n - length xs


{-@ lookupAppendLeft :: xs:List a -> ys:List a -> i:Between 0 (length xs)
                     -> {lookup i (append xs ys) = lookup i xs} @-}
lookupAppendLeft :: Eq a => List a -> List a -> Int -> Proof
lookupAppendLeft (Cons x xs) ys 0 = trivial
lookupAppendLeft (Cons _ xs) ys i = lookupAppendLeft xs ys (i-1)

{-@ lookupAppendRight :: xs:List a -> ys:List a -> i:Between 0 (length ys)
                      -> {lookup (i + length xs) (append xs ys) = lookup i ys} @-}
lookupAppendRight :: Eq a => List a -> List a -> Int -> Proof
lookupAppendRight Nil         ys i = trivial
lookupAppendRight (Cons x xs) ys i = lookupAppendRight xs ys i

{-@ takeDropAppend :: xs:List a -> n:Between 0 (length xs)
                   -> {append (take n xs) (drop n xs) == xs} @-}
takeDropAppend :: Eq a => List a -> Int -> Proof
takeDropAppend (Cons x xs) 0 = trivial
takeDropAppend (Cons x xs) n = takeDropAppend xs (n-1)
