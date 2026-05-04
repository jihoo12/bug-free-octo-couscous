{-# LANGUAGE GADTs #-}

module CubicalLambda where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- 1. Interval Syntax & DNF
--------------------------------------------------------------------------------

data I 
    = I0 | I1 
    | IVar Int 
    | Meet I I | Join I I | Neg I
    deriving (Eq, Ord)

instance Show I where
    show I0 = "0"
    show I1 = "1"
    show (IVar n) = "i" ++ show n
    show (Meet i j) = "(" ++ show i ++ " ∧ " ++ show j ++ ")"
    show (Join i j) = "(" ++ show i ++ " ∨ " ++ show j ++ ")"
    show (Neg i) = "¬" ++ show i

data Literal = Pos Int | NegVar Int deriving (Eq, Ord)

instance Show Literal where
    show (Pos n)    = "i" ++ show n
    show (NegVar n) = "¬i" ++ show n

newtype DNF = DNF { getCubes :: Set (Set Literal) } deriving (Eq, Ord)

instance Show DNF where
    show (DNF cs) 
        | Set.null cs = "0"
        | Set.null (Set.findMin cs) && Set.size cs == 1 = "1"
        | otherwise = intercalate " ∨ " (map showCube (Set.toList cs))
      where
        showCube c = if Set.null c then "1" else "(" ++ intercalate " ∧ " (map show (Set.toList c)) ++ ")"

--------------------------------------------------------------------------------
-- 2. Cubical Dependent Syntax
--------------------------------------------------------------------------------

type Name = String
type Level = Int

data Term
    = TVar Name
    | TApp Term Term
    | TAbs Name Term
    -- Universes
    | TUniv Level           -- U_n
    -- Dependent Types (Pi Types)
    | TPi Name Term Term    -- Π(x:A). B
    -- Cubical Additions
    | TInterval I           -- Symbolic Interval
    | TCube DNF             -- Normalized Interval
    -- Path Types
    | TPath Term Term Term  -- Path A u v
    | PLam Name Term        -- ⟨i⟩ t (Path abstraction)
    | PApp Term Term        -- t @ r (Path application)
    deriving (Eq)

instance Show Term where
    show t = case t of
        TVar x      -> x
        TApp f a    -> "(" ++ show f ++ " " ++ show a ++ ")"
        TAbs x b    -> "λ" ++ x ++ ". " ++ show b
        TUniv n     -> "U" ++ show n
        TPi x a b   -> "Π(" ++ x ++ ":" ++ show a ++ "). " ++ show b
        TInterval i -> show i
        TCube c     -> show c
        TPath a u v -> "Path " ++ show a ++ " " ++ show u ++ " " ++ show v
        PLam i t    -> "⟨" ++ i ++ "⟩ " ++ show t
        PApp t r    -> show t ++ " @ " ++ show r

--------------------------------------------------------------------------------
-- 3. Evaluation & Substitution
--------------------------------------------------------------------------------

-- | Capture-avoiding substitution: t[x := s]
subst :: Name -> Term -> Term -> Term
subst x s term = case term of
    TVar y      | x == y    -> s
                | otherwise -> TVar y
    TApp f a                -> TApp (subst x s f) (subst x s a)
    TAbs y b    | x == y    -> TAbs y b
                | otherwise -> TAbs y (subst x s b)
    TPi y a b   | x == y    -> TPi y (subst x s a) b
                | otherwise -> TPi y (subst x s a) (subst x s b)
    TUniv n                 -> TUniv n
    TInterval i             -> TInterval i
    TCube c                 -> TCube c
    TPath a u v             -> TPath (subst x s a) (subst x s u) (subst x s v)
    PLam i t    | x == i    -> PLam i t
                | otherwise -> PLam i (subst x s t)
    PApp t r                -> PApp (subst x s t) (subst x s r)

-- | Normalizes terms to Normal Form
eval :: Term -> Term
eval t = case t of
    TApp f a -> 
        case eval f of
            TAbs x body -> eval (subst x (eval a) body)
            f'          -> TApp f' (eval a)
    
    -- Path Beta-reduction: (⟨i⟩ t) @ r  ==>  t[i := r]
    PApp t r ->
        case eval t of
            PLam i body -> eval (subst i (eval r) body)
            t'          -> PApp t' (eval r)

    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TPath a u v -> TPath (eval a) (eval u) (eval v)
    PLam i b    -> PLam i (eval b)
    TInterval i -> TCube (evalInterval i)
    _           -> t

--------------------------------------------------------------------------------
-- 4. Interval Algebra
--------------------------------------------------------------------------------

simplify :: Set (Set Literal) -> Set (Set Literal)
simplify cubes = Set.filter (\c -> not $ any (\other -> c /= other && other `Set.isSubsetOf` c) cubes) cubes

evalInterval :: I -> DNF
evalInterval I0          = DNF Set.empty
evalInterval I1          = DNF (Set.singleton Set.empty)
evalInterval (IVar n)    = DNF (Set.singleton (Set.singleton (Pos n)))
evalInterval (Neg i)     = dnfNeg (evalInterval i)
evalInterval (Meet i j)  = dnfMeet (evalInterval i) (evalInterval j)
evalInterval (Join i j)  = dnfJoin (evalInterval i) (evalInterval j)

dnfJoin (DNF a) (DNF b)   = DNF $ simplify (Set.union a b)
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
    putStrLn "=== Cubical Lambda Calculus with Path Types ==="

    -- 1. Identity function (Standard Pi Type)
    let idType = TPi "A" (TUniv 0) (TPi "x" (TVar "A") (TVar "A"))
    let idTerm = TAbs "A" (TAbs "x" (TVar "x"))
    
    putStrLn $ "\nIdentity Type: " ++ show idType
    putStrLn $ "Identity Term: " ++ show idTerm

    -- 2. Reflexivity (Path Type)
    -- refl : Π(A:U0). Π(x:A). Path A x x
    -- refl = λA. λx. ⟨i⟩ x
    let refl = TAbs "A" (TAbs "x" (PLam "i" (TVar "x")))
    putStrLn $ "\nReflexivity (refl): " ++ show refl

    -- 3. Path Application
    -- Applying refl to a type and term, then applying an interval
    -- (refl U0 T) @ 0
    let testPath = PApp (TApp (TApp refl (TUniv 0)) (TVar "T")) (TInterval I0)
    putStrLn $ "\nEvaluating (refl U0 T) @ 0:"
    putStrLn $ "Result: " ++ show (eval testPath)

    -- 4. De Morgan in the Interval (Normalized inside a Path)
    -- ⟨i⟩ Path A (¬(i0 ∨ i1)) (¬i0 ∧ ¬i1)
    let deMorganLHS = Neg (Join (IVar 0) (IVar 1))
    let deMorganRHS = Meet (Neg (IVar 0)) (Neg (IVar 1))
    let pathDeMorgan = TPath (TUniv 0) (TInterval deMorganLHS) (TInterval deMorganRHS)
    
    putStrLn $ "\nNormalized De Morgan Interval in Type:"
    putStrLn $ "Raw: " ++ show pathDeMorgan
    putStrLn $ "Normalized: " ++ show (eval pathDeMorgan)

    -- 5. Symmetry (Function that flips a path)
    -- sym : Π(A:U0). Π(x y: A). Path A x y -> Path A y x
    -- sym = λA. λx. λy. λp. ⟨i⟩ p @ ¬i
    let sym = TAbs "A" (TAbs "x" (TAbs "y" (TAbs "p" (PLam "i" (PApp (TVar "p") (TInterval (Neg (IVar 0))))))))
    putStrLn $ "\nSymmetry term: " ++ show sym