{-# LANGUAGE GADTs #-}

module CubicalInterval where

--------------------------------------------------------------------------------
-- 1. The Interval Type (De Morgan Algebra)
--------------------------------------------------------------------------------

data I 
    = I0 
    | I1 
    | Meet I I 
    | Join I I 
    | Neg I
    deriving (Show, Eq)

-- | Deep Normalization
-- Collapses the interval logic recursively to ensure terms like 
-- Neg (Meet I0 I1) simplify to I1.
normalize :: I -> I
normalize I0 = I0
normalize I1 = I1
normalize (Neg I0) = I1
normalize (Neg I1) = I0
normalize (Neg (Neg i)) = normalize i
normalize (Neg (Meet i j)) = normalize (Join (Neg i) (Neg j)) -- De Morgan
normalize (Neg (Join i j)) = normalize (Meet (Neg i) (Neg j)) -- De Morgan
normalize (Meet i j) = 
    let i' = normalize i
        j' = normalize j
    in case (i', j') of
        (I0, _)  -> I0
        (_, I0)  -> I0
        (I1, x)  -> x
        (x, I1)  -> x
        (a, b)   | a == b -> a
                 | otherwise -> Meet a b
normalize (Join i j) = 
    let i' = normalize i
        j' = normalize j
    in case (i', j') of
        (I1, _)  -> I1
        (_, I1)  -> I1
        (I0, x)  -> x
        (x, I0)  -> x
        (a, b)   | a == b -> a
                 | otherwise -> Join a b

--------------------------------------------------------------------------------
-- 2. Paths and Squares
--------------------------------------------------------------------------------

type Path a = I -> a
type Square a = I -> I -> a

-- | Constant path (Reflexivity)[cite: 1]
refl :: a -> Path a
refl x _ = x

-- | Path Reversal (p⁻¹)[cite: 1]
rev :: Path a -> Path a
rev p i = p (normalize (Neg i))

-- | Path Composition (p ∙ q)
-- A simplified composition that switches from p to q at the midpoint.
trans :: Path a -> Path a -> Path a
trans p q i = case normalize i of
    I0 -> p I0
    I1 -> q I1
    _  -> q i -- Simplified logic for symbolic execution

--------------------------------------------------------------------------------
-- 3. Connections (Path to Square)
--------------------------------------------------------------------------------

-- | The 'connection' allows us to view a path as a square where 
-- three sides are constant and one side is the path.
connection0 :: Path a -> Square a
connection0 p i j = p (normalize (Meet i j))

connection1 :: Path a -> Square a
connection1 p i j = p (normalize (Join i j))

--------------------------------------------------------------------------------
-- 4. Main Execution and Visualization
--------------------------------------------------------------------------------

-- | Helper to print a 2D boundary of a square
printSquare :: String -> Square String -> IO ()
printSquare label sq = do
    putStrLn $ "--- " ++ label ++ " ---"
    putStrLn $ "p(0,0): " ++ sq I0 I0
    putStrLn $ "p(1,0): " ++ sq I1 I0
    putStrLn $ "p(0,1): " ++ sq I0 I1
    putStrLn $ "p(1,1): " ++ sq I1 I1
    putStrLn ""

main :: IO ()
main = do
    -- 1. Logic Simplification[cite: 1]
    let complex = Join (Meet I1 (Neg I0)) (Neg I1)
    putStrLn $ "Simplified Logic: " ++ show (normalize complex) -- Should be I1
    
    -- 2. Path Setup
    let p i = if normalize i == I0 then "Left" else "Right"
    
    -- 3. Connection Test
    -- This turns a 1D path into a 2D square using the 'Meet' operation.
    let sq = connection0 p
    printSquare "Connection Square (Meet-based)" sq
    
    -- 4. Composition Test
    let q i = if normalize i == I0 then "Right" else "Far Right"
    let composed = trans p q
    putStrLn $ "Composed Path at 0: " ++ composed I0
    putStrLn $ "Composed Path at 1: " ++ composed I1