import qualified Data.Set as Set

-- 1. Unified Data Definition
type Name = String

data Term
    = Var Name
    | App Term Term
    | Lam Name Term Term   
    | Pi  Name Term Term   
    | Kind                 -- The type of types (*)
    | Box                  -- The type of Kind (□)
    deriving (Eq)

instance Show Term where
    show (Var x)     = x
    show (App m n)   = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Lam x t e) = "λ" ++ x ++ ":" ++ show t ++ "." ++ show e
    show (Pi x t b)  = "Π" ++ x ++ ":" ++ show t ++ "." ++ show b
    show Kind        = "*"
    show Box         = "□"

-- 2. Evaluation / Normalization
substitute :: Name -> Term -> Term -> Term
substitute x n (Var y)
    | x == y    = n
    | otherwise = Var y
substitute x n (App m1 m2) = App (substitute x n m1) (substitute x n m2)
substitute x n (Lam y t e)
    | x == y    = Lam y (substitute x n t) e
    | otherwise = Lam y (substitute x n t) (substitute x n e)
substitute x n (Pi y t b)
    | x == y    = Pi y (substitute x n t) b
    | otherwise = Pi y (substitute x n t) (substitute x n b)
substitute _ _ Kind = Kind
substitute _ _ Box  = Box

reduce :: Term -> Term
reduce (App m n) =
    case reduce m of
        Lam x t e -> reduce (substitute x n e)
        m'        -> App m' (reduce n)
reduce (Pi x t b)  = Pi x (reduce t) (reduce b)
reduce (Lam x t e) = Lam x (reduce t) (reduce e)
reduce x           = x

-- 3. Type Checking Logic
type Context = [(Name, Term)]

typeOf :: Context -> Term -> Either String Term
typeOf _ Box = Left "Type Error: Box is the top of the hierarchy"
typeOf _ Kind = Right Box  -- Kind now has a type!

typeOf ctx (Var x) = 
    case lookup x ctx of
        Just t  -> Right t
        Nothing -> Left $ "Unbound variable: " ++ x

-- Rule for Pi: A and B must be types (Kind) or the universe itself (Box)
typeOf ctx (Pi x a b) = do
    sA <- typeOf ctx a
    sB <- typeOf ((x, a) : ctx) b
    -- This allows for polymorphism (Kind -> Kind)
    if (sA == Kind || sA == Box) && (sB == Kind || sB == Box)
        then Right sB 
        else Left "Type Error: Pi components must be Types or Kinds"

-- Rule for Lambda
typeOf ctx (Lam x a e) = do
    _ <- typeOf ctx a 
    b <- typeOf ((x, a) : ctx) e
    return (Pi x a b)

-- Rule for App
typeOf ctx (App m n) = do
    tM <- typeOf ctx m
    tN <- typeOf ctx n
    case reduce tM of
        Pi x a b -> 
            if reduce a == reduce tN
            then Right (reduce (substitute x n b))
            else Left $ "Type mismatch: Expected " ++ show a ++ " but got " ++ show tN
        _ -> Left $ "Type Error: " ++ show m ++ " is not a function (Pi) type"

-- 4. Main Execution
main :: IO ()
main = do
    putStrLn "--- Fixed Dependent Type System ---"

    let bool = Var "Bool"
    let ctx = [("Bool", Kind), ("True", bool), ("False", bool)]

    -- Example 1: Polymorphic Identity λA:*. λx:A. x
    let polyId = Lam "A" Kind (Lam "x" (Var "A") (Var "x"))
    
    putStrLn $ "Term: " ++ show polyId
    case typeOf ctx polyId of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e

    -- Example 2: Applying PolyId to Bool
    let appBool = App polyId bool
    putStrLn $ "\nApplying to Bool: " ++ show appBool
    case typeOf ctx appBool of
        Right t -> putStrLn $ "Type: " ++ show t
        Left e  -> putStrLn $ "Error: " ++ e
