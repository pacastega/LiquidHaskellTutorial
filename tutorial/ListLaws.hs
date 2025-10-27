{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--etabeta"    @-}

module ListLaws where

import BasicsSol
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((>>=), return, (++))

{-@ reflect return @-}
return :: a -> List a
return x = Cons x Nil

{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: List a -> List a -> List a
(++) = append

{-@ infix   >>= @-}
{-@ reflect >>= @-}
(>>=) :: List a -> (a -> List b) -> List b
Nil         >>= _ = Nil
(Cons x xs) >>= f = f x ++ (xs >>= f)

{-@ rightIdentity :: x:List a -> { x >>= return = x } @-}
rightIdentity :: List a -> Proof
rightIdentity = undefined

{-@ appendIdR :: xs:List a -> { xs ++ Nil = xs } @-}
appendIdR :: List a -> Proof
appendIdR = undefined


{-@ leftIdentity :: x:a -> f:(a -> List b) -> { return x >>= f = f x } @-}
leftIdentity :: a -> (a -> List b) -> Proof
leftIdentity = undefined

{-@ appendAssoc :: xs:List a -> ys:List a -> zs:List a
                -> { (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
appendAssoc :: List a -> List a -> List a -> Proof
appendAssoc = undefined

{-@ rightDistributive :: xs:List a -> ys:List a -> f:(a -> List b)
                      -> { xs ++ ys >>= f = (xs >>= f) ++ (ys >>= f) } @-}
rightDistributive :: List a -> List a -> (a -> List b) -> Proof
rightDistributive = undefined

{-@ associativity :: x:List a -> f:(a -> List a) -> g:(a -> List a)
                  -> { (x >>= f) >>= g = x >>= (\r:a -> f r >>= g) } @-}
associativity :: List a -> (a -> List a) -> (a -> List a) -> Proof
associativity = undefined
