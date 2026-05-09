module Cubical.Syntax
    ( Term(..)
    , Name, Level
    , showTerm
    , shift, subst, beta
    ) where

import Cubical.Interval (I, DNF)

type Name  = String
type Level = Int

--------------------------------------------------------------------------------
-- Term Syntax
--------------------------------------------------------------------------------

data Term
    = TVar Int
    | TApp Term Term
    | TAbs Name Term
    | TUniv Level
    | TIntervalTy
    | TPi Name Term Term
    | TInterval I
    | TCube DNF
    | TPath Term Term Term
    | PLam Name Term
    | PApp Term Term
    | THComp Term Term Term Term
    | TEquiv Term Term
    | TMkEquiv Term Term Term Term Term Term
    | TEquivFwd Term Term
    | TUa Term
    | TTransport Term Term
    | TGlue Term Term Term
    | TGlueElem Term Term Term
    | TUnglue Term Term Term
    | TSigma Name Term Term
    | TPair Term Term
    | TFst Term
    | TSnd Term
    deriving (Eq)

showTerm :: [Name] -> Term -> String
showTerm env t = case t of
    TVar i      -> if i < length env then env !! i else "#" ++ show i
    TApp f a    -> "(" ++ showTerm env f ++ " " ++ showTerm env a ++ ")"
    TAbs x b    -> "λ" ++ x ++ ". " ++ showTerm (x:env) b
    TUniv n     -> "U" ++ show n
    TIntervalTy -> "𝕀"
    TPi x a b   -> "Π(" ++ x ++ ":" ++ showTerm env a ++ "). " ++ showTerm (x:env) b
    TInterval i -> show i
    TCube c     -> show c
    TPath a u v -> "Path " ++ showTerm env a ++ " " ++ showTerm env u ++ " " ++ showTerm env v
    PLam i b    -> "⟨" ++ i ++ "⟩ " ++ showTerm (i:env) b
    PApp p r    -> showTerm env p ++ " @ " ++ showTerm env r
    THComp a phi u u0 ->
        "hcomp " ++ showTerm env a
        ++ " [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env u ++ ") "
        ++ showTerm env u0
    TEquiv a b ->
        "Equiv " ++ showTerm env a ++ " " ++ showTerm env b
    TMkEquiv a b f g eta eps ->
        "mkEquiv " ++ showTerm env a ++ " " ++ showTerm env b
        ++ " " ++ showTerm env f ++ " " ++ showTerm env g
        ++ " " ++ showTerm env eta ++ " " ++ showTerm env eps
    TEquivFwd e x ->
        "equivFwd (" ++ showTerm env e ++ ") " ++ showTerm env x
    TUa e ->
        "ua (" ++ showTerm env e ++ ")"
    TTransport p x ->
        "transport (" ++ showTerm env p ++ ") " ++ showTerm env x
    TGlue a phi te ->
        "Glue " ++ showTerm env a
        ++ " [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env te ++ ")"
    TGlueElem phi t a ->
        "glue [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env t ++ ") "
        ++ showTerm env a
    TUnglue phi te g ->
        "unglue [" ++ showTerm env phi ++ "] "
        ++ "(" ++ showTerm env te ++ ") "
        ++ showTerm env g
    TSigma x a b ->
        "Σ(" ++ x ++ ":" ++ showTerm env a ++ "). " ++ showTerm (x:env) b
    TPair a b ->
        "(" ++ showTerm env a ++ " , " ++ showTerm env b ++ ")"
    TFst p ->
        "fst " ++ showTerm env p
    TSnd p ->
        "snd " ++ showTerm env p

instance Show Term where
    show = showTerm []

--------------------------------------------------------------------------------
-- Shift / Subst / Beta
--------------------------------------------------------------------------------

shift :: Int -> Int -> Term -> Term
shift d c term = case term of
    TVar i      -> TVar (if i >= c then i + d else i)
    TApp f a    -> TApp (shift d c f) (shift d c a)
    TAbs x b    -> TAbs x (shift d (c+1) b)
    TPi x a b   -> TPi x (shift d c a) (shift d (c+1) b)
    TUniv n     -> TUniv n
    TIntervalTy -> TIntervalTy
    TInterval i -> TInterval i
    TCube cu    -> TCube cu
    TPath a u v -> TPath (shift d c a) (shift d c u) (shift d c v)
    PLam x b    -> PLam x (shift d (c+1) b)
    PApp p r    -> PApp (shift d c p) (shift d c r)
    THComp a phi u u0 ->
        THComp (shift d c a) (shift d c phi) (shift d c u) (shift d c u0)
    TEquiv a b ->
        TEquiv (shift d c a) (shift d c b)
    TMkEquiv a b f g eta eps ->
        TMkEquiv (shift d c a) (shift d c b) (shift d c f) (shift d c g)
                 (shift d c eta) (shift d c eps)
    TEquivFwd e x ->
        TEquivFwd (shift d c e) (shift d c x)
    TUa e ->
        TUa (shift d c e)
    TTransport p x ->
        TTransport (shift d c p) (shift d c x)
    TGlue a phi te ->
        TGlue (shift d c a) (shift d c phi) (shift d c te)
    TGlueElem phi t a ->
        TGlueElem (shift d c phi) (shift d c t) (shift d c a)
    TUnglue phi te g ->
        TUnglue (shift d c phi) (shift d c te) (shift d c g)
    TSigma x a b ->
        TSigma x (shift d c a) (shift d (c+1) b)
    TPair a b ->
        TPair (shift d c a) (shift d c b)
    TFst p ->
        TFst (shift d c p)
    TSnd p ->
        TSnd (shift d c p)

subst :: Int -> Term -> Term -> Term
subst j s term = case term of
    TVar i
        | i == j    -> s
        | otherwise -> TVar i
    TApp f a    -> TApp (subst j s f) (subst j s a)
    TAbs x b    -> TAbs x (subst (j+1) (shift 1 0 s) b)
    TPi x a b   -> TPi x (subst j s a) (subst (j+1) (shift 1 0 s) b)
    TUniv n     -> TUniv n
    TIntervalTy -> TIntervalTy
    TInterval i -> TInterval i
    TCube cu    -> TCube cu
    TPath a u v -> TPath (subst j s a) (subst j s u) (subst j s v)
    PLam x b    -> PLam x (subst (j+1) (shift 1 0 s) b)
    PApp p r    -> PApp (subst j s p) (subst j s r)
    THComp a phi u u0 ->
        THComp (subst j s a) (subst j s phi) (subst j s u) (subst j s u0)
    TEquiv a b ->
        TEquiv (subst j s a) (subst j s b)
    TMkEquiv a b f g eta eps ->
        TMkEquiv (subst j s a) (subst j s b) (subst j s f) (subst j s g)
                 (subst j s eta) (subst j s eps)
    TEquivFwd e x ->
        TEquivFwd (subst j s e) (subst j s x)
    TUa e ->
        TUa (subst j s e)
    TTransport p x ->
        TTransport (subst j s p) (subst j s x)
    TGlue a phi te ->
        TGlue (subst j s a) (subst j s phi) (subst j s te)
    TGlueElem phi t a ->
        TGlueElem (subst j s phi) (subst j s t) (subst j s a)
    TUnglue phi te g ->
        TUnglue (subst j s phi) (subst j s te) (subst j s g)
    TSigma x a b ->
        TSigma x (subst j s a) (subst (j+1) (shift 1 0 s) b)
    TPair a b ->
        TPair (subst j s a) (subst j s b)
    TFst p ->
        TFst (subst j s p)
    TSnd p ->
        TSnd (subst j s p)

beta :: Term -> Term -> Term
beta body arg = shift (-1) 0 (subst 0 (shift 1 0 arg) body)