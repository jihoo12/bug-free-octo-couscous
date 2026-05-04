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
    deriving (Eq)

instance Show Term where
    show (Var i)     = show i
    show (App m n)   = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e) = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)  = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind        = "*"
    show Box         = "□"

-- 2. De Bruijn Shifting and Substitution
shift :: Int -> Int -> Term -> Term
shift d c (Var i)     = if i >= c then Var (i + d) else Var i
shift d c (App m n)   = App (shift d c m) (shift d c n)
shift d c (Lam x t e) = Lam x (shift d c t) (shift d (c + 1) e)
shift d c (Pi x t b)  = Pi x (shift d c t) (shift d (c + 1) b)
shift _ _ Kind        = Kind
shift _ _ Box         = Box

substitute :: Index -> Term -> Term -> Term
substitute j n (Var i)
    | i == j    = n
    | otherwise = Var i
substitute j n (App m1 m2) = App (substitute j n m1) (substitute j n m2)
substitute j n (Lam x t e) =
    Lam x (substitute j n t) (substitute (j + 1) (shift 1 0 n) e)
substitute j n (Pi x t b)  =
    Pi x (substitute j n t) (substitute (j + 1) (shift 1 0 n) b)
substitute _ _ Kind = Kind
substitute _ _ Box  = Box

-- 3. Evaluation
reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam _ _ e -> reduce (shift (-1) 0 (substitute 0 (shift 1 0 n) e))
        m'        -> App m' (reduce n)
reduce (Pi x t b)  = Pi x (reduce t) (reduce b)
reduce (Lam x t e) = Lam x (reduce t) (reduce e)
reduce x           = x

betaEquals :: Term -> Term -> Bool
betaEquals t1 t2 = reduce t1 == reduce t2

-- 4. Type Checking
type Context = [Term]

-- Helper to check if a term is a "sort" (Kind or Box)
checkIsSort :: Context -> Term -> Either String Term
checkIsSort _ Kind = Right Box
checkIsSort _ Box  = Right Box
checkIsSort ctx t  = do
    tType <- typeOf ctx t
    let reducedType = reduce tType
    if reducedType == Kind || reducedType == Box
        then Right reducedType
        else Left $ "Type Error: " ++ show t ++ " is not a valid type/kind"

typeOf :: Context -> Term -> Either String Term
typeOf _ Box = Left "Type Error: Box is the top of the hierarchy"
typeOf _ Kind = Right Box

typeOf ctx (Var i)
    | i < length ctx = Right (shift (i + 1) 0 (ctx !! i))
    | otherwise      = Left $ "Unbound index: " ++ show i

typeOf ctx (Pi x a b) = do
    _ <- checkIsSort ctx a
    checkIsSort (a : ctx) b

typeOf ctx (Lam x a e) = do
    _ <- checkIsSort ctx a
    b <- typeOf (a : ctx) e
    return (Pi x a b)

typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi _ a b ->
            if betaEquals a tN
            then Right (shift (-1) 0 (substitute 0 (shift 1 0 n) b))
            else Left $ "Type mismatch: Expected " ++ show a ++ " but got " ++ show tN
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function type"

-- 5. Main
main :: IO ()
main = do
    putStrLn "--- De Bruijn Type System with Beta-Equivalence ---"
    -- Context: index 0 is 'Bool' which is a Kind (*)
    let ctx = [Kind] 

    -- Identity: λA:*. λx:A. x
    let identity = Lam "A" Kind (Lam "x" (Var 0) (Var 0))
    
    -- A complex argument that reduces to 'Bool' (index 0)
    -- (λT:*. T) Bool
    -- Note: Domain is Kind (*) because Bool is a Kind
    let identityOnTypes = Lam "T" Kind (Var 0)
    let complexTypeArg = App identityOnTypes (Var 0) 
    
    -- Applying (λA:*. λx:A. x) to the complex 'Bool'
    -- This requires beta-reduction of the argument type to match
    let testTerm = App identity complexTypeArg

    case typeOf ctx testTerm of
        Right t -> do
            putStrLn $ "Term: " ++ show testTerm
            putStrLn $ "Success! Type: " ++ show (reduce t)
        Left e  -> putStrLn $ "Error: " ++ e