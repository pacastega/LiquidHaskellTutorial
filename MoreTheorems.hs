module MoreTheorems where

{-@ reflect rotate @-}
{-@ rotate :: xs:List a -> n:Between 0 (length xs) -> List a @-}
rotate :: List a -> Int -> List a
rotate xs n = append (drop n xs) (take n xs)

{-@ rotateCorrect :: xs:List a -> n:Between 0 (length xs)
                  -> i:Between 0 (length xs)
                  -> {lookup i (rotate xs n) = lookup ((i+n) mod (length xs)) xs}
@-}
rotateCorrect :: Eq a => List a -> Int -> Int -> Proof
rotateCorrect xs n i = let ys = take n xs; zs = drop n xs in undefined

{-@ lookupAppendLeft :: xs:List a -> ys:List a -> i:Between 0 (length xs)
                     -> {lookup i (append xs ys) = lookup i xs} @-}
lookupAppendLeft :: Eq a => List a -> List a -> Int -> Proof
lookupAppendLeft (Cons x xs) ys 0 = undefined
lookupAppendLeft (Cons _ xs) ys i = undefined

{-@ lookupAppendRight :: xs:List a -> ys:List a -> i:Between 0 (length ys)
                      -> {lookup (i + length xs) (append xs ys) = lookup i ys} @-}
lookupAppendRight :: Eq a => List a -> List a -> Int -> Proof
lookupAppendRight Nil         ys i = undefined
lookupAppendRight (Cons x xs) ys i = undefined

{-@ takeDropAppend :: xs:List a -> n:Between 0 (length xs)
                   -> {append (take n xs) (drop n xs) == xs} @-}
takeDropAppend :: Eq a => List a -> Int -> Proof
takeDropAppend (Cons x xs) 0 = undefined
takeDropAppend (Cons x xs) n = undefined
