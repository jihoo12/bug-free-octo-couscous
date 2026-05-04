module Main where

type Name = String
type Index = Int

data Term
    = Var Index
    | App Term Term
    | Lam Name Term Term
    | Pi  Name Term Term
    | Kind
    | Box
    -- Cubical Additions
    | Interval          -- The type I
    | I0                -- The endpoint 0
    | I1                -- The endpoint 1
    | PathP Term Term Term -- PathP (A : I -> *) x y
    | PLam Term Term    -- Path abstraction: <name> e (where name is for display)
    | PApp Term Term    -- Path application: e @ i
    deriving (Eq)

instance Show Term where
    show (Var i)       = show i
    show (App m n)     = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e)   = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)    = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind          = "*"
    show Box           = "□"
    show Interval      = "I"
    show I0            = "0"
    show I1            = "1"
    show (PathP a x y) = "PathP " ++ show a ++ " " ++ show x ++ " " ++ show y
    show (PLam _ e)    = "<_> " ++ show e
    show (PApp m i)    = show m ++ " @ " ++ show i

-- 1. De Bruijn Shifting and Substitution
shift :: Int -> Int -> Term -> Term
shift d c (Var i)       = if i >= c then Var (i + d) else Var i
shift d c (App m n)     = App (shift d c m) (shift d c n)
shift d c (Lam x t e)   = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)    = Pi x (shift d c t) (shift d (c + 1) b)
shift d c (PathP a x y) = PathP (shift d c a) (shift d c x) (shift d c y)
shift d c (PLam t e)    = PLam (shift d c t) (shift d (c + 1) e)
shift d c (PApp m i)    = PApp (shift d c m) (shift d c i)
shift _ _ t             = t

substitute :: Index -> Term -> Term -> Term
substitute j n (Var i)
    | i == j    = n
    | otherwise = Var i
substitute j n (App m1 m2) = App (substitute j n m1) (substitute j n m2)
substitute j n (Lam x t e) =
    Lam x (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (Pi x t b)  =
    Pi x (substitute j n t) (substitute (j + 1) (shift 1 0 n) b)
substitute j n (PathP a x y) = 
    PathP (substitute j n a) (substitute j n x) (substitute j n y)
substitute j n (PLam t e) = 
    PLam (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (PApp m i) = 
    PApp (substitute j n m) (substitute j n i)
substitute _ _ t = t

-- 2. Evaluation
reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
reduce (PApp m i) =
    let i' = reduce i
    in case reduce m of
        -- Cubical reduction: (PLam e) @ 0 -> e[0], (PLam e) @ 1 -> e[1]
        PLam _ e -> case i' of
            I0 -> reduce (shift (-1) 0 (substitute 0 I0 e))
            I1 -> reduce (shift (-1) 0 (substitute 0 I1 e))
            _  -> PApp (reduce m) i'
        m' -> PApp m' i'
reduce (Pi x t b)    = Pi x (reduce t) (reduce b)
reduce (Lam x t e)   = Lam x (reduce t) (reduce e)
reduce (PathP a x y) = PathP (reduce a) (reduce x) (reduce y)
reduce (PLam t e)    = PLam (reduce t) (reduce e)
reduce x             = x

betaEquals :: Term -> Term -> Bool
betaEquals t1 t2 = reduce t1 == reduce t2

-- 3. Consistency and PTS Rules
type Context = [Term]

allowedRules :: Term -> Term -> Either String Term
allowedRules Kind Kind = Right Kind
allowedRules Kind Box  = Right Box
allowedRules Box Kind  = Right Kind
allowedRules Box Box   = Right Box
allowedRules s1 s2     = Left $ "PTS Rule violation: (" ++ show s1 ++ ", " ++ show s2 ++ ")"

-- 4. Type Checking
checkIsSort :: Context -> Term -> Either String Term
checkIsSort ctx t = do
    tType <- typeOf ctx t
    case reduce tType of
        Kind -> Right Kind
        Box  -> Right Box
        _    -> Left $ "Consistency Error: " ++ show t ++ " is not a Sort"

typeOf :: Context -> Term -> Either String Term
typeOf _ Box  = Left "Type Error: Box is untypable"
typeOf _ Kind = Right Box
typeOf _ Interval = Right Box
typeOf _ I0 = Right Interval
typeOf _ I1 = Right Interval

typeOf ctx (Var i)
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    s1 <- checkIsSort ctx a
    s2 <- checkIsSort (a : ctx) b
    allowedRules s1 s2

typeOf ctx (Lam x a e) = do
    _ <- checkIsSort ctx a
    b <- typeOf (a : ctx) e
    return $ Pi x a b

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi _ a b ->
            if betaEquals a tN
            then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
            else Left $ "Type mismatch in App"
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function"

typeOf ctx (PathP a x y) = do
    ta <- typeOf ctx a
    case reduce ta of
        Pi _ Interval Kind -> do
            tx <- typeOf ctx x
            ty <- typeOf ctx y
            let type0 = reduce (App a I0)
            let type1 = reduce (App a I1)
            if betaEquals tx type0 && betaEquals ty type1
                then Right Kind
                else Left "PathP boundary mismatch"
        _ -> Left "PathP requires a type family over Interval"

typeOf ctx (PLam a e) = do
    _ <- typeOf ctx a -- a: I -> Kind
    -- The body e is checked with the interval variable in context
    _ <- typeOf (Interval : ctx) e
    let start = reduce (shift (-1) 0 (substitute 0 I0 e))
    let end   = reduce (shift (-1) 0 (substitute 0 I1 e))
    return $ PathP a start end

typeOf ctx (PApp m i) = do
    tm <- typeOf ctx m
    ti <- typeOf ctx i
    case (reduce tm, ti) of
        (PathP a _ _, Interval) -> Right (reduce (App a i))
        _ -> Left "PApp expects a Path and an Interval coordinate"

-- 5. Main with PathP Example
main :: IO ()
main = do
    putStrLn "--- Cubical Type System Test ---"
    
    -- Let A be a constant type (Kind)
    -- aFamily = λi:I. A
    let aFamily = Lam "i" Interval (Var 1) -- Var 1 points to A in ctx
    let ctx = [Kind] -- Index 0 is A
    
    -- Create a reflexivity path for some x:A
    -- p = <_> x
    let x = Var 1 -- x:A
    let ctx2 = [Var 0, Kind] -- Index 0 is x, Index 1 is A
    let refl = PLam (shift 1 0 aFamily) (Var 1)
    
    putStrLn $ "Term: " ++ show refl
    case typeOf ctx2 refl of
        Right t -> do
            putStrLn $ "Type: " ++ show t
            putStrLn $ "Reduced @ 0: " ++ show (reduce (PApp refl I0))
            putStrLn $ "Reduced @ 1: " ++ show (reduce (PApp refl I1))
        Left e  -> putStrLn $ "Error: " ++ e
-- current goal 
-- switch to cumulative hierarchy of universes
-- switch to cubical type theory plan.txt
-- implement Inductive Types
