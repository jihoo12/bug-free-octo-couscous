{-# LANGUAGE GADTs #-}

module CubicalLambda where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- 1. Interval Syntax & DNF (Your Original Logic)
--------------------------------------------------------------------------------

data I 
    = I0 | I1 
    | IVar Int 
    | Meet I I | Join I I | Neg I
    deriving (Show, Eq, Ord)

data Literal = Pos Int | NegVar Int deriving (Eq, Ord)

instance Show Literal where
    show (Pos n)    = "i" ++ show n
    show (NegVar n) = "¬i" ++ show n

type Cube = Set Literal
newtype DNF = DNF { getCubes :: Set Cube } deriving (Eq, Ord)

instance Show DNF where
    show (DNF cs) 
        | Set.null cs = "0"
        | Set.null (Set.findMin cs) && Set.size cs == 1 = "1"
        | otherwise = intercalate " ∨ " (map showCube (Set.toList cs))
      where
        showCube c = if Set.null c then "1" else "(" ++ intercalate " ∧ " (map show (Set.toList c)) ++ ")"

--------------------------------------------------------------------------------
-- 2. Lambda Calculus Syntax
--------------------------------------------------------------------------------

-- | Names for lambda variables
type Name = String

data Term
    = TVar Name             -- Standard Lambda Variable
    | TApp Term Term        -- Application (f x)
    | TAbs Name Term        -- Lambda Abstraction (λx. t)
    | TInterval I           -- An embedded Interval expression
    | TCube DNF             -- An evaluated Interval (normalized)
    deriving (Show)

--------------------------------------------------------------------------------
-- 3. Evaluation & Substitution
--------------------------------------------------------------------------------

-- | Simple substitution for Lambda Calculus: t[x := s]
subst :: Name -> Term -> Term -> Term
subst x s t = case t of
    TVar y      | x == y    -> s
                | otherwise -> TVar y
    TApp f a                -> TApp (subst x s f) (subst x s a)
    TAbs y body | x == y    -> TAbs y body -- Shadowing
                | otherwise -> TAbs y (subst x s body)
    TInterval i             -> TInterval i
    TCube c                 -> TCube c

-- | Normalizes both the Lambda structure and the Interval logic
evalTerm :: Term -> Term
evalTerm (TVar x) = TVar x
evalTerm (TAbs x t) = TAbs x (evalTerm t)
evalTerm (TApp f a) = 
    case evalTerm f of
        TAbs x body -> evalTerm (subst x (evalTerm a) body)
        f'          -> TApp f' (evalTerm a)
evalTerm (TInterval i) = TCube (evalInterval i) -- Normalize interval logic here
evalTerm (TCube c)     = TCube c

--------------------------------------------------------------------------------
-- 4. Interval Algebra (Refactored from your code)
--------------------------------------------------------------------------------

simplify :: Set Cube -> Set Cube
simplify cubes = Set.filter (\c -> not $ any (\other -> c /= other && other `Set.isSubsetOf` c) cubes) cubes

evalInterval :: I -> DNF
evalInterval I0          = DNF Set.empty
evalInterval I1          = DNF (Set.singleton Set.empty)
evalInterval (IVar n)    = DNF (Set.singleton (Set.singleton (Pos n)))
evalInterval (Neg i)     = dnfNeg (evalInterval i)
evalInterval (Meet i j)  = dnfMeet (evalInterval i) (evalInterval j)
evalInterval (Join i j)  = dnfJoin (evalInterval i) (evalInterval j)

dnfJoin (DNF a) (DNF b) = DNF $ simplify (Set.union a b)
dnfMeet (DNF as) (DNF bs) = DNF $ simplify $ Set.fromList [ Set.union a b | a <- Set.toList as, b <- Set.toList bs ]
dnfNeg (DNF cubes) 
    | Set.null cubes = DNF $ Set.singleton Set.empty
    | otherwise = foldr dnfMeet (DNF $ Set.singleton Set.empty) (map negCube (Set.toList cubes))
  where
    negCube c = DNF $ Set.fromList [Set.singleton (negLit l) | l <- Set.toList c]
    negLit (Pos n) = NegVar n
    negLit (NegVar n) = Pos n

--------------------------------------------------------------------------------
-- 5. Demonstration
--------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "=== Lambda Calculus + Cubical Intervals ==="

    -- Define an interval expression: (i0 ∨ ¬i0)
    let intervalExpr = Join (IVar 0) (Neg (IVar 0))
    
    -- Define a lambda: λx. (x ∧ i1)
    -- In cubical terms, this could represent a path transformation
    let lambdaPath = TAbs "x" (TApp (TVar "x") (TInterval I1))

    -- Example 1: Identity Application
    -- (λx. x) (i0 ∨ ¬i0)
    let identity = TAbs "x" (TVar "x")
    let test1 = TApp identity (TInterval intervalExpr)
    
    putStrLn $ "Input:  (λx. x) (i0 ∨ ¬i0)"
    putStrLn $ "Result: " ++ show (evalTerm test1)

    -- Example 2: Constant Function
    -- (λx. i0) (i1)
    let constFunc = TAbs "x" (TInterval I0)
    let test2 = TApp constFunc (TInterval I1)
    
    putStrLn $ "\nInput:  (λx. i0) (i1)"
    putStrLn $ "Result: " ++ show (evalTerm test2)

    -- Example 3: Nested Normalization
    -- Applying a double negation to a variable within a lambda
    let test3 = TInterval (Neg (Neg (IVar 5)))
    putStrLn $ "\nInput:  ¬¬i5"
    putStrLn $ "Result: " ++ show (evalTerm test3)