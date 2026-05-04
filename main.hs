{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import qualified Data.Map as Map
import Data.Map (Map)

-- 1. Syntax for the Interval (I)
type Name = String

data Interval 
  = I0 
  | I1 
  | IVar Name 
  deriving (Eq, Show)

-- 2. Face Lattice (Simplified Formulae)
-- In a real system, you'd need DNF or BDDs. Here we use simple equality atoms.
data Formula 
  = FDir Interval 
  | FEq Name Interval 
  | FAnd Formula Formula 
  | FOr Formula Formula
  | FTop | FBot
  deriving (Eq, Show)

-- 3. Core Terms
data Term
  = Var Name
  | Universe
  | Pi Name Term Term
  | Lam Name Term
  | App Term Term
  -- Cubical: Glue A [phi -> (T, f)]
  | Glue Term Formula Term 
  -- GlueElem: the constructor
  | GlueElem Term Formula Term
  -- Unglue: the destructor
  | Unglue Term Formula Term
  deriving (Show)

-- 4. Evaluation Environment
type Env = Map Name Value

data Value
  = VUniverse
  | VPi Name Value (Value -> Value)
  | VLam Name (Value -> Value)
  | VPair Value Value
  -- VGlue A phi (T, f)
  | VGlue Value Formula Value
  | VGlueElem Value Formula Value
  | VNeutral Neutral
  
data Neutral
  = NVar Name
  | NApp Neutral Value
  | NUnglue Neutral Formula Value

-- 5. The "Magic" of Glue: Evaluation Logic
-- This is where the computation rules for Univalence live.
eval :: Term -> Env -> Value
eval (Universe) _    = VUniverse
eval (Var x) env     = env Map.! x
eval (Lam x t) env   = VLam x (\v -> eval t (Map.insert x v env))
eval (App t1 t2) env = apply (eval t1 env) (eval t2 env)
eval (Glue a phi eq) env = VGlue (eval a env) phi (eval eq env)
eval (GlueElem t phi u) env = VGlueElem (eval t env) phi (eval u env)
eval (Unglue g phi eq) env = unglue (eval g env) phi (eval eq env)

apply :: Value -> Value -> Value
apply (VLam _ f) v = f v
apply (VNeutral n) v = VNeutral (NApp n v)
apply _ _ = error "Invalid application"

-- The key reduction: unglue (GlueElem t phi u) phi eq = u if phi is 1
unglue :: Value -> Formula -> Value -> Value
unglue (VGlueElem t phi u) formula eq =
    if formula == FTop -- Simplified: if the face is active
    then u 
    else t
unglue (VNeutral n) phi eq = VNeutral (NUnglue n phi eq)
unglue _ _ _ = error "Unglue requires a Glue element or Neutral"

-- 6. Example Usage
-- Representing: Glue A (i=1) (B, f)
exampleGlue :: Term
exampleGlue = Glue (Var "A") (FEq "i" I1) (Var "equiv_B_A")

main :: IO ()
main = do
    putStrLn "Mini-Cubical Glue Evaluator initialized."
    print exampleGlue