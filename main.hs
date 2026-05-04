module Main where

import Data.List (find)
import Control.Monad (when)

-- | 1. Data Definitions
type Name = String
type Index = Int
type Context = [Term]

data Term
    = Var Index
    | App Term Term
    | Lam Name Term Term
    | Pi  Name Term Term
    | Universe Int          
    | Interval | I0 | I1    
    | IAnd Term Term | IOr Term Term | INot Term             
    | PathP Term Term Term  
    | PLam Term Term        
    | PApp Term Term        
    | Partial Term Term      
    | Side Term [(Term, Term)] 
    | Glue Term Term Term   
    | Total Term Term Term  
    | Unglue Term Term      
    | Comp Term Term Term  
    | Sigma Name Term Term
    | Pair Term Term
    | Fst Term | Snd Term
    deriving (Eq)

-- | 2. Improved Traversal Engine
-- Instead of repeating logic for shift and substitute, we use a generic mapper.
mapTerm :: (Int -> Index -> Term) -> Int -> Term -> Term
mapTerm f c t = case t of
    Var i          -> f c i
    App m n        -> App (go m) (go n)
    Lam x t e      -> Lam x (go t) (mapTerm f (c + 1) e)
    Pi x t b       -> Pi x (go t) (mapTerm f (c + 1) b)
    PathP a x y    -> PathP (go a) (go x) (go y)
    PLam t e       -> PLam (go t) (mapTerm f (c + 1) e)
    PApp m i       -> PApp (go m) (go i)
    IAnd p q       -> IAnd (go p) (go q)
    IOr p q        -> IOr (go p) (go q)
    INot p         -> INot (go p)
    Partial p a    -> Partial (go p) (go a)
    Side p bs      -> Side (go p) [(go bp, go bt) | (bp, bt) <- bs]
    Glue a p f     -> Glue (go a) (go p) (go f)
    Total p t a    -> Total (go p) (go t) (go a)
    Unglue t p     -> Unglue (go t) (go p)
    Comp a p u     -> Comp (go a) (go p) (go u)
    Sigma x a b    -> Sigma x (go a) (mapTerm f (c + 1) b)
    Pair t1 t2     -> Pair (go t1) (go t2)
    Fst t          -> Fst (go t)
    Snd t          -> Snd (go t)
    _              -> t
  where go = mapTerm f c

shift :: Int -> Int -> Term -> Term
shift d = mapTerm (\c i -> if i >= c then Var (i + d) else Var i)

substitute :: Index -> Term -> Term -> Term
substitute j n = mapTerm (\c i -> if i == j + c then shift c 0 n else Var i) 0

-- | 3. Reduction & Composition Logic
reduceFormula :: Term -> Term
reduceFormula t = case t of
    IAnd p q -> case (reduceFormula p, reduceFormula q) of
        (I1, x) -> x; (x, I1) -> x; (I0, _) -> I0; (_, I0) -> I0; (a, b) -> if a == b then a else IAnd a b
    IOr p q -> case (reduceFormula p, reduceFormula q) of
        (I1, _) -> I1; (_, I1) -> I1; (I0, x) -> x; (x, I0) -> x; (a, b) -> if a == b then a else IOr a b
    INot p -> case reduceFormula p of
        I1 -> I0; I0 -> I1; p' -> INot p'
    _ -> t

reduce :: Term -> Term
reduce term = case term of
    App m n -> case reduce m of
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
    PApp m i -> case (reduce m, reduce i) of
        (PLam _ e, i') -> reduce (shift (-1) 0 (substitute 0 i' e))
        (m', i')       -> PApp m' i'
    Fst t -> case reduce t of
        Pair a _ -> reduce a
        t'       -> Fst t'
    Snd t -> case reduce t of
        Pair _ b -> reduce b
        t'       -> Snd t'
    Comp a phi u -> evalComp (reduce a) (reduceFormula phi) (reduce u)
    -- Simplified recursive reduction for other terms
    Pi x a b    -> Pi x (reduce a) (reduce b)
    Lam x a e   -> Lam x (reduce a) (reduce e)
    Sigma x a b -> Sigma x (reduce a) (reduce b)
    Pair a b    -> Pair (reduce a) (reduce b)
    _           -> term

-- Helper for the "Fill" operation
fill :: Term -> Term -> Term -> Term
fill a phi u = PLam a $ Comp 
    (PLam Interval (App (shift 1 0 a) (IAnd (Var 1) (Var 0))))
    (IOr (shift 1 0 phi) (INot (Var 0)))
    (Side (IOr (shift 1 0 phi) (INot (Var 0))) 
        [(shift 1 0 phi, PApp (shift 1 0 u) (Var 0)), (INot (Var 0), PApp (shift 1 0 u) I0)])

evalComp :: Term -> Term -> Term -> Term
evalComp a phi u = case phi of
    I1 -> reduce (PApp u I1)
    _  -> case reduce (App a I0) of
        Pi x b c -> 
            let fillB i = fill b phi (PLam Interval (Var 1)) -- Simplification for refactor
            in Lam x (App (shift 1 0 b) I0) (Comp (PLam Interval (App (shift 1 1 a) (Var 0))) phi u) -- Recursive placeholder
        Sigma x b c ->
            let u1 = PLam Interval (Fst (PApp (shift 1 0 u) (Var 0)))
                c1 = Comp (PLam Interval (App (shift 1 0 b) (Var 0))) phi u1
                f1 = fill (PLam Interval (App (shift 1 0 b) (Var 0))) phi u1
                u2 = PLam Interval (Snd (PApp (shift 1 0 u) (Var 0)))
                -- Second component type depends on the fill of the first
                pathC2 = PLam Interval $ substitute 0 (PApp (shift 1 0 f1) (Var 0)) (shift 1 1 c)
            in Pair c1 (Comp pathC2 phi u2)
        _ -> Comp a phi u

-- | 4. Type Checking
typeOf :: Context -> Term -> Either String Term
typeOf ctx t = case t of
    Universe n -> Right (Universe (n + 1))
    Interval   -> Right (Universe 0)
    I0         -> Right Interval
    I1         -> Right Interval
    Var i      -> if i < length ctx then Right (shift (i + 1) 0 (ctx !! i)) else Left "Scope error"
    
    Pi x a b -> do
        checkIsType ctx a
        checkIsType (a : ctx) b
        return $ Universe 0 -- Simplified level
        
    Lam x a e -> do
        checkIsType ctx a
        b <- typeOf (a : ctx) e
        return $ Pi x a b
        
    App m n -> do
        tm <- typeOf ctx m
        case reduce tm of
            Pi _ a b -> do
                tn <- typeOf ctx n
                if tn == a then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
                else Left "Type mismatch in App"
            _ -> Left "Not a function"

    Sigma x a b -> do
        checkIsType ctx a
        checkIsType (a : ctx) b
        return $ Universe 0

    Pair t1 t2 -> do
        a <- typeOf ctx t1
        b <- typeOf (a : ctx) t2 -- This is dependent!
        return $ Sigma "x" a (shift (-1) 1 b)

    _ -> Left $ "Type checking not fully implemented for: " ++ show t

checkIsType :: Context -> Term -> Either String ()
checkIsType ctx t = do
    ty <- typeOf ctx t
    case reduce ty of
        Universe _ -> return ()
        _          -> Left "Expected a type"

-- | 5. Show Instance and Main
instance Show Term where
    show t = case t of
        Var i       -> show i
        Universe n  -> "U" ++ show n
        Lam x t e   -> "λ(" ++ x ++ ":" ++ show t ++ ")." ++ show e
        Pi x a b    -> "Π(" ++ x ++ ":" ++ show a ++ ")." ++ show b
        App m n     -> "(" ++ show m ++ " " ++ show n ++ ")"
        Pair a b    -> "(" ++ show a ++ ", " ++ show b ++ ")"
        Sigma x a b -> "Σ(" ++ x ++ ":" ++ show a ++ ")." ++ show b
        Interval    -> "I"
        _           -> "..." -- Compacted for brevity

main :: IO ()
main = do
    let testTerm = Lam "A" (Universe 0) (Lam "x" (Var 0) (Var 0))
    putStrLn $ "Testing Identity: " ++ show testTerm
    case typeOf [] testTerm of
        Right ty -> putStrLn $ "Type: " ++ show ty
        Left err -> putStrLn $ "Error: " ++ err