{-@ LIQUID "--reflection" @-}
module TheoremProvingSol where

import BasicsSol
import Prelude hiding (length, lookup, append, take, drop, id, (.), map)
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ fmapId :: xs:List a -> { map id xs == xs } @-}
fmapId :: List a -> Proof

fmapId Nil
  =   map id Nil
  === Nil
  *** QED

fmapId (Cons x xs)
  = map id (Cons x xs)
  === Cons (id x) (map id xs)
  === Cons x (map id xs) ? fmapId xs
  === Cons x xs
  *** QED

{-@ infix . @-}
{-@ reflect (.) @-}
(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \x -> f (g x)

{-@ fmapCompose :: f:(b -> c) -> g:(a -> b) -> xs:List a
                -> { map f (map g xs) = map (f . g) xs } @-}
fmapCompose :: (b -> c) -> (a -> b) -> List a -> Proof

fmapCompose f g xs = case xs of
  Nil         -> map f (map g Nil)
             === map f Nil
             === Nil
             === map (f . g) Nil
             *** QED
  (Cons x xs) -> map f (map g (Cons x xs))
             === map f (Cons (g x) (map g xs))
             === Cons (f (g x)) (map f (map g xs))
             === Cons ((f . g) x) (map f (map g xs))
               ? fmapCompose f g xs
             === Cons ((f . g) x) (map (f . g) xs)
             === map (f . g) (Cons x xs)
             *** QED


--------------------------------------------------------------------------------
-- EXERCISE: Given data Pair a b = Pair a b, define the map function for Pair
-- with respect to one of the type parameters, and prove that it satisfies the
-- same properties as the map on lists.

data Pair a b = Pair a b

{-@ reflect mapFst @-}
{-@ mapFst :: (a -> c) -> Pair a b -> Pair c b @-}
mapFst :: (a -> c) -> Pair a b -> Pair c b
mapFst f (Pair x y) = Pair (f x) y

{-@ fmapFstId :: p:Pair a b -> { mapFst id p == p } @-}
fmapFstId :: Pair a b -> Proof
fmapFstId (Pair x y)
  =   mapFst id (Pair x y)
  === Pair (id x) y
  === Pair x y
  *** QED

{-@ fmapFstCompose :: f:(a -> c) -> g:(d -> a) -> p:Pair d b
                   -> { mapFst f (mapFst g p) = mapFst (f . g) p } @-}
fmapFstCompose :: (a -> c) -> (d -> a) -> Pair d b -> Proof
fmapFstCompose f g (Pair x y)
  =   mapFst f (mapFst g (Pair x y))
  === mapFst f (Pair (g x) y)
  === Pair (f (g x)) y
  === Pair ((f . g) x) y
  === mapFst (f . g) (Pair x y)
  *** QED
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- EXERCISE: Write the theorem that says that appending the empty list on the
-- right does nothing.
{-@ appendNilR :: xs:List a -> { append xs Nil == xs } @-}
appendNilR :: List a -> Proof
appendNilR xs = case xs of
  Nil         -> append Nil Nil
             === Nil
             *** QED
  (Cons x xs) -> append (Cons x xs) Nil
             === Cons x (append xs Nil)
               ? appendNilR xs
             === Cons x xs
             *** QED
--------------------------------------------------------------------------------

{-@ LIQUID "--ple" @-}

{-@ fmapCompose' :: f:(b -> c) -> g:(a -> b) -> xs:List a
                -> { map f (map g xs) = map (f . g) xs } @-}
fmapCompose' :: (b -> c) -> (a -> b) -> List a -> Proof
fmapCompose' f g xs = case xs of
        Nil         -> trivial
        (Cons x xs) -> fmapCompose' f g xs

--------------------------------------------------------------------------------
-- EXERCISE: Use PLE to redo the proofs that you did before.

{-@ fmapId' :: xs:List a -> { map id xs == xs } @-}
fmapId' :: List a -> Proof
fmapId' xs = case xs of
        Nil         -> trivial
        (Cons x xs) -> fmapId' xs

{-@ mapFstId' :: p:Pair a b -> { mapFst id p == p } @-}
mapFstId' :: Pair a b -> Proof
mapFstId' (Pair x y) = trivial

{-@ fmapFstCompose' :: f:(a -> c) -> g:(d -> a) -> p:Pair d b
                   -> { mapFst f (mapFst g p) = mapFst (f . g) p } @-}
fmapFstCompose' :: (a -> c) -> (d -> a) -> Pair d b -> Proof
fmapFstCompose' f g (Pair x y) = trivial

{-@ appendNilR' :: xs:List a -> { append xs Nil == xs } @-}
appendNilR' :: List a -> Proof
appendNilR' xs = case xs of
        Nil         -> trivial
        (Cons x xs) -> appendNilR' xs
--------------------------------------------------------------------------------
