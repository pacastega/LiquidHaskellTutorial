{-@ LIQUID "--reflection" @-}
module TheoremProving where

import BasicsSol
import Prelude hiding (length, lookup, append, take, drop, id, (.), map)
import Language.Haskell.Liquid.ProofCombinators

-- identity function
{-@ reflect id @-}
id :: a -> a
id x = x

-- function composition
{-@ infix . @-}
{-@ reflect (.) @-}
(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \x -> f (g x)

-- proof that mapping with the identity function does nothing
fmapId :: List a -> Proof
fmapId xs = undefined

-- proof that mapping over (f . g) is the same as mapping first g and then f
fmapCompose :: (b -> c) -> (a -> b) -> List a -> Proof
fmapCompose f g xs = undefined


--------------------------------------------------------------------------------
-- EXERCISE: Given data Pair a b = Pair a b, define the map function for Pair
-- with respect to one of the type parameters, and prove that it satisfies the
-- same properties as the map on lists.

data Pair a b = Pair a b
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- EXERCISE: Write the theorem that says that appending the empty list on the
-- right does nothing.
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- EXERCISE: Use PLE to redo the proofs that you did before.
--------------------------------------------------------------------------------
