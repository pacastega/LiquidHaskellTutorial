{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--reflection" @-}
module StackMachine where

{-@ infix : @-}
{-@ infix ++ @-}

import Prelude hiding ((++))

import Language.Haskell.Liquid.ProofCombinators

-- PART 1: The stack machine language ------------------------------------------

-- our supported values will be integers and booleans
data Value = VInt Int | VBool Bool
  deriving (Show, Eq)

-- values will be placed on a stack
data Stack = SEmpty | SCons Value Stack
  deriving (Show, Eq)

-- we need to assign types to the values
data Ty = TInt | TBool
  deriving (Show, Eq)

{-@ reflect inferValueType @-}
inferValueType :: Value -> Ty
inferValueType _ = undefined

-- to type a stack of values, we need a stack of types
data TStack = TEmpty | TCons Ty TStack
  deriving (Show, Eq)

{-@ reflect inferStackType @-}
inferStackType :: Stack -> TStack
inferStackType SEmpty = TEmpty
inferStackType (SCons v s) = TCons (inferValueType v) (inferStackType s)

-- our stack language will have 4 instructions:
data Instruction = PUSH Int -- push an integer to the top of the stack
                 | ADD      -- pop last two values, add them, push result
                 | SUB      -- pop last two values, subtract them, push result
                 | TEST     -- pop last two values, push whether they are equal
  deriving (Show, Eq)

-- if we tried to run an instruction on a stack with a given type,
-- a. will we be able to run it?
-- b. if we succeed, what type stack will we get?
{-@ reflect tyCheck1 @-}
tyCheck1 :: TStack -> Instruction -> Maybe TStack
tyCheck1 s                           (PUSH n) = Just (TCons TInt s)
tyCheck1 (TCons TInt (TCons TInt s)) ADD      = Just (TCons TInt s)
tyCheck1 (TCons TInt (TCons TInt s)) SUB      = Just (TCons TInt s)
tyCheck1 (TCons TInt (TCons TInt s)) TEST     = Just (TCons TBool s)
tyCheck1 _                           _        = Nothing

-- repeat 'tyCheck1' for running a list of instructions sequentially
{-@ reflect tyCheck @-}
tyCheck :: TStack -> [Instruction] -> Maybe TStack
tyCheck s (i:is) | Just s' <- tyCheck1 s i = tyCheck s' is
tyCheck s [] = Just s
tyCheck _ _ = Nothing

-- if we run an instruction on a given stack,
-- a. how can we ensure that we will be able to run it?
-- b. after running it, what stack will we get?
{-@ reflect stepStack @-}
stepStack :: Stack -> Instruction -> Stack
stepStack s (PUSH n) = SCons (VInt n) s
stepStack (SCons (VInt x) (SCons (VInt y) s)) ADD  = SCons (VInt (x+y))     s
stepStack (SCons (VInt x) (SCons (VInt y) s)) SUB  = SCons (VInt (y-x))     s
stepStack (SCons (VInt x) (SCons (VInt y) s)) TEST = SCons (VBool (x == y)) s
stepStack _ _ = undefined -- ???

-- repeat 'stepStack' for running a list of instructions sequentially
{-@ reflect evalStack @-}
evalStack :: Stack -> [Instruction] -> Stack
evalStack s [] = s
evalStack s (i:is) = evalStack (stepStack s i) is

-- PART 2: The high-level expression language ----------------------------------

data Expr = LInt Int       -- literal integers
          | LBool Bool     -- literal booleans
          | EAdd Expr Expr -- addition
          | ESub Expr Expr -- subtraction
          | EEq Expr Expr  -- checking for equality

{-@ reflect inferType @-}
inferType :: Expr -> Maybe Ty
inferType (LInt _) = Just TInt
inferType (LBool _) = Just TBool
inferType (EAdd e1 e2)
  | Just TInt <- inferType e1
  , Just TInt <- inferType e2
  = Just TInt
inferType (ESub e1 e2)
  | Just TInt <- inferType e1
  , Just TInt <- inferType e2
  = Just TInt
inferType (EEq e1 e2)
  | Just TInt <- inferType e1
  , Just TInt <- inferType e2
  = Just TBool
inferType _ = Nothing

-- for simplicity, let's define an alias for expressions with inferred type 'T'
{-@ type TypedExpr T = Expr @-}

-- when we evaluate an expression, can we ensure that we will get a value of the
-- correct type?
{-@ reflect evalExpr @-}
{-@ evalExpr :: t:Ty
             -> e:TypedExpr t
             -> Value @-}
evalExpr :: Ty -> Expr -> Value
evalExpr _ (LInt n) = VInt n
evalExpr _ (LBool b) = VBool b
evalExpr _ (EAdd e1 e2) = case (evalExpr TInt e1, evalExpr TInt e2) of
  (VInt v1, VInt v2) -> VInt (v1 + v2)
  _ -> undefined -- ???
evalExpr _ (ESub e1 e2) = case (evalExpr TInt e1, evalExpr TInt e2) of
  (VInt v1, VInt v2) -> VInt (v1 - v2)
  _ -> undefined -- ???
evalExpr _ (EEq e1 e2) = case (evalExpr TInt e1, evalExpr TInt e2) of
  (VInt v1, VInt v2) -> VBool (v1 == v2)
  _ -> undefined -- ???


-- PART 3: Compiling expressions to the stack machine language -----------------

{-@ reflect compile @-}
{-@ compile :: t:Ty -> TypedExpr t -> [Instruction] @-}
compile :: Ty -> Expr -> [Instruction]
compile _ (LInt  n) = [PUSH n]
compile _ (LBool True)  = [PUSH 1, PUSH 1, TEST]
compile _ (LBool False) = [PUSH 0, PUSH 1, TEST]
compile _ (EAdd   e1 e2) = compile TInt e1 ++ compile TInt e2 ++ [ADD]
compile _ (ESub   e1 e2) = compile TInt e1 ++ compile TInt e2 ++ [SUB]
compile _ (EEq    e1 e2) = compile TInt e1 ++ compile TInt e2 ++ [TEST]


-- when we compile a well-typed expression,
-- a. the resulting program should be able to run on any stack
-- b. after running the program, the result should be the original stack with
--    the new value (of the correct type) pushed on top
{-@ compileWellTyped :: t:Ty -> e:TypedExpr t -> ts:TStack
                     -> Proof @-}
compileWellTyped :: Ty -> Expr -> TStack -> Proof
compileWellTyped _ (LInt  n) ts = undefined
compileWellTyped _ (LBool True)  ts = undefined
compileWellTyped _ (LBool False) ts = undefined
compileWellTyped _ (EAdd e1 e2) ts = undefined
compileWellTyped _ (ESub   e1 e2) ts = undefined
compileWellTyped _ (EEq    e1 e2) ts = undefined


-- when we compile a well-typed expression, running the resulting program on a
-- stack should be equivalent to just pushing the value of the expression on the
-- top of the stack
{-@ compileCorrect :: t:Ty -> e:TypedExpr t
          -> {s:Stack | isJust (tyCheck (inferStackType s) (compile t e))}
          -> Proof @-}
compileCorrect :: Ty -> Expr -> Stack -> Proof
compileCorrect _ (LInt n) _ = undefined
compileCorrect _ (LBool True) _ = undefined
compileCorrect _ (LBool False) _ = undefined
compileCorrect _ (EAdd e1 e2) s = undefined
compileCorrect _ (ESub e1 e2) s = undefined
compileCorrect _ (EEq e1 e2) s = undefined


-- APPENDIX: Useful functions --------------------------------------------------

{-@ reflect isJust @-}
isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing = False

{-@ reflect fromJust @-}
{-@ fromJust :: {v:Maybe a | isJust v} -> a @-}
fromJust :: Maybe a -> a
fromJust (Just x) = x

{-@ reflect (++) @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | len zs = len xs + len ys} @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

infixr 5 ++

{-@ liquidAssert :: {b:Bool | b} -> {b} @-}
liquidAssert :: Bool -> Proof
liquidAssert _ = ()
