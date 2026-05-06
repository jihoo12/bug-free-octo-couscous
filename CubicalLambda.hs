{-# LANGUAGE GADTs #-}

module CubicalLambda where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- Interval Syntax & DNF
--------------------------------------------------------------------------------

data I
    = I0 | I1
    | IVar Int
    | Meet I I | Join I I | Neg I
    deriving (Eq, Ord)

instance Show I where
    show I0         = "0"
    show I1         = "1"
    show (IVar n)   = "i" ++ show n
    show (Meet i j) = "(" ++ show i ++ " ∧ " ++ show j ++ ")"
    show (Join i j) = "(" ++ show i ++ " ∨ " ++ show j ++ ")"
    show (Neg i)    = "¬" ++ show i

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
        showCube c =
            if Set.null c
                then "1"
                else "(" ++ intercalate " ∧ " (map show (Set.toList c)) ++ ")"

--------------------------------------------------------------------------------
-- Cubical Dependent Syntax
--------------------------------------------------------------------------------

-- We keep Name only for hints shown in pretty-printing; it has no semantic role.
type Name  = String
type Level = Int

-- | De Bruijn representation.
--
--   Variables are non-negative integers that count the number of binders
--   between the use site and the binder:
--
--     λ. λ. 0      -- the inner λ's own variable
--     λ. λ. 1      -- the outer λ's variable
--
--   Every binder (TAbs, TPi, PLam) carries an optional Name hint purely for
--   pretty-printing; it is ignored by all semantic operations.
data Term
    = TVar Int              -- de Bruijn index
    | TApp Term Term
    | TAbs Name Term        -- λ(hint). body    — binds de Bruijn 0 in body
    -- Universes
    | TUniv Level           -- U_n
    -- Interval pseudo-type (𝕀 lives outside the universe hierarchy)
    | TIntervalTy           -- the "type" of interval expressions
    -- Dependent Types (Pi Types)
    | TPi Name Term Term    -- Π(hint:A). B     — binds de Bruijn 0 in B
    -- Cubical Additions
    | TInterval I           -- Symbolic Interval
    | TCube DNF             -- Normalized Interval
    -- Path Types
    | TPath Term Term Term  -- Path A u v
    | PLam Name Term        -- ⟨hint⟩ t  (Path abstraction, binds interval 0 in t)
    | PApp Term Term        -- t @ r  (Path application)
    -- Kan Composition
    | THComp Term Term Term Term
    -- hcomp A φ u u₀
    --
    -- Glue Types
    | TGlue Term Term Term
    -- Glue A φ T_e
    --   A   : Term  — the base type
    --   φ   : Term  — the face/cofibration (interval term)
    --   T_e : Term  — a partial element of Σ(T:U). Equiv T A, defined on φ
    --
    -- Typing rule:
    --   Γ ⊢ A : U_n   Γ ⊢ φ : 𝕀   Γ,φ ⊢ T_e : Σ(T:U_n). Equiv T A
    --   ──────────────────────────────────────────────────────────────
    --   Γ ⊢ Glue A φ T_e : U_n
    --
    -- β-rules:
    --   Glue A ⊤ (T, e)  ≡  T
    --   Glue A ⊥ _       ≡  A
    --
    | TGlueElem Term Term Term
    -- glue φ t a
    --   φ : Term  — the face
    --   t : Term  — partial element of T (defined on φ)
    --   a : Term  — element of A (base type)
    --
    -- Typing rule:
    --   Γ ⊢ φ : 𝕀   Γ,φ ⊢ t : T   Γ ⊢ a : A   φ ⊢ e(t) ≡ a
    --   ────────────────────────────────────────────────────────
    --   Γ ⊢ glue φ t a : Glue A φ (T, e)
    --
    -- β-rules:
    --   glue ⊤ t a  ≡  t
    --   glue ⊥ t a  ≡  a
    --
    | TUnglue Term Term Term
    -- unglue φ T_e g
    --   φ   : Term  — the face
    --   T_e : Term  — partial (T, e) defined on φ
    --   g   : Term  — element of Glue A φ T_e
    --
    -- Typing rule:
    --   Γ ⊢ g : Glue A φ T_e
    --   ─────────────────────
    --   Γ ⊢ unglue φ T_e g : A
    --
    -- β-rules:
    --   unglue ⊤ (T, e) g  ≡  e(g)   (apply the equivalence)
    --   unglue ⊥ _      g  ≡  g      (g already lives in A)
    deriving (Eq)

-- | Pretty-print a term, recovering readable names from a name-hint stack.
--   Each binder pushes its hint; TVar i looks up index i in the stack.
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

instance Show Term where
    show = showTerm []

--------------------------------------------------------------------------------
-- Evaluation & Substitution  (de Bruijn)
--------------------------------------------------------------------------------

-- | @shift d c t@ increments every free variable in @t@ whose index is ≥ @c@
--   by @d@.  This is the standard "lifting" operation needed to slide a term
--   under a new binder without accidentally capturing free variables.
--
--   * @d@  — the increment (usually +1 when going under one new binder)
--   * @c@  — the cutoff: indices below @c@ are bound by binders already
--             counted in the current context, so they must not be touched
shift :: Int -> Int -> Term -> Term
shift d c term = case term of
    TVar i      -> TVar (if i >= c then i + d else i)
    TApp f a    -> TApp (shift d c f) (shift d c a)
    -- Binders increase the cutoff by 1 for their sub-term
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
    TGlue a phi te ->
        TGlue (shift d c a) (shift d c phi) (shift d c te)
    TGlueElem phi t a ->
        TGlueElem (shift d c phi) (shift d c t) (shift d c a)
    TUnglue phi te g ->
        TUnglue (shift d c phi) (shift d c te) (shift d c g)

-- | @subst j s t@ replaces every free occurrence of de Bruijn index @j@ in
--   @t@ with the term @s@, properly adjusting indices so that no variable
--   capture can occur.
--
--   The standard single-step recipe for going under a binder is:
--
--   1. Increment all free variables of @s@ by 1 (shift by 1 at cutoff 0),
--      so that @s@'s own free variables skip over the new binder.
--   2. Recurse with @j+1@ as the target index.
--
--   After the whole substitution the binder itself disappears, so every
--   remaining free variable ≥ j must be decremented by 1 — this is handled
--   by the @shift (-1) j@ call after eliminating the outermost binder (see
--   @beta@ below).
subst :: Int -> Term -> Term -> Term
subst j s term = case term of
    TVar i
        | i == j    -> s
        | otherwise -> TVar i
    TApp f a    -> TApp (subst j s f) (subst j s a)
    -- Going under a binder: lift s over the new binder; target index += 1
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
    TGlue a phi te ->
        TGlue (subst j s a) (subst j s phi) (subst j s te)
    TGlueElem phi t a ->
        TGlueElem (subst j s phi) (subst j s t) (subst j s a)
    TUnglue phi te g ->
        TUnglue (subst j s phi) (subst j s te) (subst j s g)

-- | β-reduce a redex: given the body of a binder and the argument,
--   substitute de Bruijn 0 with the argument and then lower all remaining
--   free indices by 1 (since the binder has been consumed).
--
--   @beta body arg = shift (-1) 0 (subst 0 (shift 1 0 arg) body)@
--
--   The inner @shift 1 0 arg@ protects @arg@'s free variables while it
--   travels under the (now-about-to-disappear) binder; the outer
--   @shift (-1) 0@ removes the slot left by the consumed binder.
beta :: Term -> Term -> Term
beta body arg = shift (-1) 0 (subst 0 (shift 1 0 arg) body)

-- | Normalizes terms to Normal Form
eval :: Term -> Term
eval t = case t of
    TApp f a ->
        case eval f of
            TAbs _ body -> eval (beta body (eval a))
            f'          -> TApp f' (eval a)

    -- Path Beta-reduction: (⟨i⟩ t) @ r  ==>  t[i := r]
    PApp t r ->
        case eval t of
            PLam _ body -> eval (beta body (eval r))
            t'          -> PApp t' (eval r)

    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TPath a u v -> TPath (eval a) (eval u) (eval v)
    PLam i b    -> PLam i (eval b)
    TInterval i -> TCube (evalInterval i)

    -- ── Kan Composition ────────────────────────────────────────────────────────
    -- Evaluate the face formula first; apply the two β-rules when φ is ⊤ or ⊥.
    THComp aTy phi tube base ->
        let phi' = eval phi
            -- φ ≡ ⊤  iff  its DNF is the single empty-conjunction cube {∅}
            isTop = phi' == TCube (DNF (Set.singleton Set.empty))
            -- φ ≡ ⊥  iff  its DNF has no cubes at all
            isBot = phi' == TCube (DNF Set.empty)
        in if isTop
           -- β-rule (⊤): hcomp A ⊤ (⟨i⟩ t) u₀  ≡  t[i := 1]
           then case eval tube of
                    PLam _ body -> eval (beta body (TInterval I1))
                    tube'       -> PApp tube' (TInterval I1)
           else if isBot
           -- β-rule (⊥): hcomp A ⊥ u u₀  ≡  u₀
           then eval base
           -- Otherwise leave it in weak-head-normal form
           else THComp (eval aTy) phi' (eval tube) (eval base)
    -- All remaining constructors are already in normal form

    -- ── Glue Types ──────────────────────────────────────────────────────────────
    -- β-rules for Glue A φ T_e:
    --   φ ≡ ⊤  →  Glue reduces to the fibre type T (first component of T_e)
    --   φ ≡ ⊥  →  Glue reduces to the base type A
    TGlue aTy phi te ->
        let phi' = eval phi
            isTop = phi' == TCube (DNF (Set.singleton Set.empty))
            isBot = phi' == TCube (DNF Set.empty)
        in if isTop
           then eval te          -- Glue A ⊤ T_e  ≡  T_e  (the fibre type on the face)
           else if isBot
           then eval aTy         -- Glue A ⊥ _    ≡  A
           else TGlue (eval aTy) phi' (eval te)

    -- ── glue element introduction ────────────────────────────────────────────────
    -- β-rules for glue φ t a:
    --   φ ≡ ⊤  →  glue reduces to the partial element t
    --   φ ≡ ⊥  →  glue reduces to the base element a
    TGlueElem phi t a ->
        let phi' = eval phi
            isTop = phi' == TCube (DNF (Set.singleton Set.empty))
            isBot = phi' == TCube (DNF Set.empty)
        in if isTop
           then eval t           -- glue ⊤ t a  ≡  t
           else if isBot
           then eval a           -- glue ⊥ t a  ≡  a
           else TGlueElem phi' (eval t) (eval a)

    -- ── unglue element elimination ───────────────────────────────────────────────
    -- β-rules for unglue φ T_e g:
    --   φ ≡ ⊤  →  unglue applies the equivalence function e to g
    --             In this minimal checker we represent e as the identity on T_e
    --             (a full univalence proof would wire in the actual equiv map)
    --   φ ≡ ⊥  →  unglue is the identity: g is already in A
    TUnglue phi te g ->
        let phi' = eval phi
            isTop = phi' == TCube (DNF (Set.singleton Set.empty))
            isBot = phi' == TCube (DNF Set.empty)
        in if isTop
           then eval g           -- unglue ⊤ (T,e) g  ≡  e(g)  (identity equiv here)
           else if isBot
           then eval g           -- unglue ⊥ _     g  ≡  g
           else TUnglue phi' (eval te) (eval g)
    _ -> t


--------------------------------------------------------------------------------
-- Interval Algebra
--------------------------------------------------------------------------------

simplify :: Set (Set Literal) -> Set (Set Literal)
simplify cubes =
    Set.filter
        (\c -> not $ any (\other -> c /= other && other `Set.isSubsetOf` c) cubes)
        cubes

evalInterval :: I -> DNF
evalInterval I0         = DNF Set.empty
evalInterval I1         = DNF (Set.singleton Set.empty)
evalInterval (IVar n)   = DNF (Set.singleton (Set.singleton (Pos n)))
evalInterval (Neg i)    = dnfNeg (evalInterval i)
evalInterval (Meet i j) = dnfMeet (evalInterval i) (evalInterval j)
evalInterval (Join i j) = dnfJoin (evalInterval i) (evalInterval j)

dnfJoin :: DNF -> DNF -> DNF
dnfJoin (DNF a) (DNF b) = DNF $ simplify (Set.union a b)

dnfMeet :: DNF -> DNF -> DNF
dnfMeet (DNF as) (DNF bs) =
    DNF $ simplify $ Set.fromList
        [ Set.union a b | a <- Set.toList as, b <- Set.toList bs ]

dnfNeg :: DNF -> DNF
dnfNeg (DNF cubes)
    | Set.null cubes = DNF $ Set.singleton Set.empty
    | otherwise =
        foldr dnfMeet (DNF $ Set.singleton Set.empty)
              (map negCube (Set.toList cubes))
  where
    negCube c   = DNF $ Set.fromList [Set.singleton (negLit l) | l <- Set.toList c]
    negLit (Pos n)    = NegVar n
    negLit (NegVar n) = Pos n

--------------------------------------------------------------------------------
-- Bidirectional Type Checker
--------------------------------------------------------------------------------

-- | The interval pseudo-type sentinel. Used as the stored type for interval
--   variables in the context (introduced by PLam and checkInterval).
intervalTy :: Term
intervalTy = TIntervalTy

-- | Typing context: a stack of (hint-name, type) pairs.
--   The head of the list is the most-recently-bound variable (de Bruijn 0).
--   Looking up de Bruijn index i retrieves element i from the head.
--   Types stored in the context are already shifted to be valid at the
--   depth where they were introduced; when we retrieve a type at depth d
--   we must shift it by d to be valid at the use site.
type Ctx = [(Name, Term)]

-- ---------------------------------------------------------------------------
-- Type Errors
-- ---------------------------------------------------------------------------

data TypeError
    = UnboundVariable Name
    | TypeMismatch Term Term   -- expected, got
    | ExpectedPi   Term        -- the non-Pi type we found
    | ExpectedPath Term        -- the non-Path type we found
    | ExpectedUniverse Term    -- the non-universe type we found
    | NotAnInterval Term       -- term that should be an interval expression
    | CannotInfer Term         -- term that needs a type annotation to check
    | Other String
    deriving (Eq)

instance Show TypeError where
    show e = case e of
        UnboundVariable x  ->
            "  Unbound variable: '" ++ x ++ "'"
        TypeMismatch ex got ->
            "  Type mismatch\n    expected : " ++ show ex
            ++ "\n    got      : " ++ show got
        ExpectedPi ty ->
            "  Expected a Π-type, but found:\n    " ++ show ty
        ExpectedPath ty ->
            "  Expected a Path type, but found:\n    " ++ show ty
        ExpectedUniverse ty ->
            "  Expected a universe U_n, but found:\n    " ++ show ty
        NotAnInterval t ->
            "  Expected an interval expression (𝕀), but got:\n    " ++ show t
        CannotInfer t ->
            "  Cannot infer type of term without annotation:\n    " ++ show t
            ++ "\n  (Tip: use 'check' instead of 'infer', or add a type annotation)"
        Other msg ->
            "  " ++ msg

-- ---------------------------------------------------------------------------
-- Context Helpers
-- ---------------------------------------------------------------------------

-- | Extend the context with a new binding (push onto the stack).
--   The new binding becomes de Bruijn index 0; all existing indices shift up.
extendCtx :: Name -> Term -> Ctx -> Ctx
extendCtx x ty ctx = (x, ty) : ctx

-- | Look up de Bruijn index @i@ in the context.
--   The type is stored at the depth it was introduced; we shift it by @i+1@
--   so that its own free variables refer correctly to the current depth.
lookupCtx :: Int -> Ctx -> Either TypeError Term
lookupCtx i ctx
    | i < 0 || i >= length ctx =
        Left (UnboundVariable ("#" ++ show i))
    | otherwise =
        let (_, ty) = ctx !! i
        in Right (shift (i + 1) 0 ty)

-- | Definitional equality: normalize both sides and compare.
definitionallyEqual :: Term -> Term -> Bool
definitionallyEqual t1 t2 = eval t1 == eval t2

requireEqual :: Term -> Term -> Either TypeError ()
requireEqual expected got
    | definitionallyEqual expected got = Right ()
    | otherwise = Left (TypeMismatch (eval expected) (eval got))

-- | Infer the type of t, assert it is some U_n, return n.
requireUniverse :: Ctx -> Term -> Either TypeError Level
requireUniverse ctx t = do
    ty <- infer ctx t
    case eval ty of
        TUniv n -> Right n
        other   -> Left (ExpectedUniverse other)

-- ---------------------------------------------------------------------------
-- Interval Validity
-- ---------------------------------------------------------------------------

-- | Assert that a term is an interval expression.
--   TInterval / TCube are syntactically intervals.
--   A variable bound with intervalTy is also an interval (introduced by PLam).
checkInterval :: Ctx -> Term -> Either TypeError ()
checkInterval _   (TInterval _) = Right ()
checkInterval _   (TCube _)     = Right ()
checkInterval ctx t = do
    ty <- infer ctx t
    if ty == intervalTy
        then Right ()
        else Left (NotAnInterval t)

-- ---------------------------------------------------------------------------
-- Type Inference  (Γ ⊢ t ⇒ T)
-- ---------------------------------------------------------------------------

-- | Synthesize the type of @t@ in context @ctx@.
--   Call 'check' for introduction forms (TAbs, PLam) which need a known type.
infer :: Ctx -> Term -> Either TypeError Term

-- ─── Variable ───────────────────────────────────────────────────────────────
-- Γ(i) = T
-- ──────────────
--  Γ ⊢ i ⇒ T
infer ctx (TVar i) = lookupCtx i ctx

-- ─── Universe ───────────────────────────────────────────────────────────────
--  Γ ⊢ U_n ⇒ U_{n+1}
infer _   (TUniv n) = Right (TUniv (n + 1))

-- ─── Application ────────────────────────────────────────────────────────────
-- Γ ⊢ f ⇒ Π(x:A).B    Γ ⊢ a ⇐ A
-- ─────────────────────────────────
--      Γ ⊢ f a ⇒ B[0:=a]
infer ctx (TApp f a) = do
    fTy <- infer ctx f
    case eval fTy of
        TPi _ aTy bTy -> do
            check ctx a aTy
            -- Substitute the argument for the bound variable (de Bruijn 0) in B
            return $ eval (beta bTy a)
        other -> Left (ExpectedPi other)

-- ─── Π Formation ────────────────────────────────────────────────────────────
-- Γ ⊢ A ⇒ U_i    Γ, _:A ⊢ B ⇒ U_j
-- ───────────────────────────────────
--    Γ ⊢ Π(_:A).B ⇒ U_{max i j}
infer ctx (TPi x aTy bTy) = do
    i <- requireUniverse ctx aTy
    j <- requireUniverse (extendCtx x (eval aTy) ctx) bTy
    return $ TUniv (max i j)

-- ─── Path Formation ─────────────────────────────────────────────────────────
-- Γ ⊢ A ⇒ U_n    Γ ⊢ u ⇐ A    Γ ⊢ v ⇐ A
-- ──────────────────────────────────────────
--        Γ ⊢ Path A u v ⇒ U_n
infer ctx (TPath aTy u v) = do
    n <- requireUniverse ctx aTy
    let aTy' = eval aTy
    check ctx u aTy'
    check ctx v aTy'
    return $ TUniv n

-- ─── Path Elimination ───────────────────────────────────────────────────────
-- Γ ⊢ p ⇒ Path A u v    r : 𝕀
-- ──────────────────────────────
--       Γ ⊢ p @ r ⇒ A
infer ctx (PApp p r) = do
    pTy <- infer ctx p
    case eval pTy of
        TPath aTy _ _ -> do
            checkInterval ctx r
            return $ eval aTy
        other -> Left (ExpectedPath other)

-- ─── Interval pseudo-types ──────────────────────────────────────────────────
--  Interval expressions inhabit the pseudo-type 𝕀 (outside universe hierarchy)
infer _   (TInterval _)  = Right intervalTy
infer _   (TCube _)      = Right intervalTy
-- 𝕀 itself is a pseudo-kind; we return it as its own "type" so that
-- checkInterval can compare against intervalTy without hitting an error.
infer _   TIntervalTy    = Right TIntervalTy

-- ─── Introduction forms require a known type ────────────────────────────────
infer _   t@(TAbs _ _) = Left (CannotInfer t)
infer _   t@(PLam _ _) = Left (CannotInfer t)

-- ─── Glue Type Formation ──────────────────────────────────────────────────────
-- Γ ⊢ A : U_n    Γ ⊢ φ : 𝕀    Γ, φ ⊢ T_e : U_n
-- ─────────────────────────────────────────────────
--        Γ ⊢ Glue A φ T_e : U_n
--
-- (In full CCHM T_e should be Σ(T:U_n). Equiv T A; here we simply require
--  T_e : U_n, trusting the user to supply a proper fibre type.)
infer ctx (TGlue aTy phi te) = do
    n  <- requireUniverse ctx aTy
    checkInterval ctx phi
    m  <- requireUniverse ctx te
    return $ TUniv (max n m)

-- ─── Unglue Elimination ───────────────────────────────────────────────────────
-- Γ ⊢ g : Glue A φ T_e
-- ────────────────────────
-- Γ ⊢ unglue φ T_e g : A
infer ctx (TUnglue phi te g) = do
    checkInterval ctx phi
    gTy <- infer ctx g
    case eval gTy of
        TGlue aTy _ _ -> return (eval aTy)
        other         -> Left (Other $
            "unglue: expected argument of Glue type, got: " ++ show other)

-- ─── Kan Composition ─────────────────────────────────────────────────────────
-- Γ ⊢ A : U_n    Γ ⊢ φ : 𝕀    Γ, i:𝕀 ⊢ u_body : A    Γ ⊢ u₀ : A
-- ──────────────────────────────────────────────────────────────────────────────
--               Γ ⊢ hcomp A φ (⟨i⟩ u_body) u₀ ⇒ A
--
-- Note: The boundary coherence condition  φ ⊢ u₀ ≡ u@0  is recorded here but
-- not enforced algorithmically, as it requires a "restriction" judgement that
-- lies outside this minimal checker's scope.
infer ctx (THComp aTy phi tube base) = do
    _n     <- requireUniverse ctx aTy
    let aTy' = eval aTy
    -- φ must be an interval expression (lives outside the universe hierarchy)
    checkInterval ctx phi
    -- The base cap must inhabit A
    check ctx base aTy'
    -- The tube must be a path abstraction whose body inhabits A
    case eval tube of
        PLam i body ->
            -- Extend context with a fresh interval variable for the tube
            check (extendCtx i intervalTy ctx) body aTy'
        tube' -> do
            -- If the tube is not a PLam (e.g. a stuck variable), infer its type
            -- and require it to be a Path in A
            tubeTy <- infer ctx tube'
            case eval tubeTy of
                TPath a _ _
                    | definitionallyEqual a aTy' -> return ()
                other -> Left (ExpectedPath other)
    return aTy'

-- ---------------------------------------------------------------------------
-- Type Checking  (Γ ⊢ t ⇐ T)
-- ---------------------------------------------------------------------------

-- | Verify that @t@ has type @ty@ in context @ctx@.
check :: Ctx -> Term -> Term -> Either TypeError ()

-- ─── Lambda Introduction ─────────────────────────────────────────────────────
-- Γ, _:A ⊢ b ⇐ B
-- ──────────────────────────
-- Γ ⊢ λ_.b ⇐ Π(_:A).B
--
-- In de Bruijn style both binders introduce index 0; no renaming is needed.
check ctx (TAbs x body) ty =
    case eval ty of
        TPi _ aTy bTy -> do
            let aTy' = eval aTy
            check (extendCtx x aTy' ctx) body bTy
        other -> Left (ExpectedPi other)

-- ─── Path Introduction ────────────────────────────────────────────────────────
-- Γ, _:𝕀 ⊢ body ⇐ A    body[0:=0] ≡ u    body[0:=1] ≡ v
-- ────────────────────────────────────────────────────────
--            Γ ⊢ ⟨_⟩ body ⇐ Path A u v
check ctx (PLam i body) ty =
    case eval ty of
        TPath aTy u v -> do
            let aTy' = eval aTy
            -- Boundary check using beta-substitution of endpoints
            let bodyAt0 = eval (beta body (TInterval I0))
            let bodyAt1 = eval (beta body (TInterval I1))
            requireEqual (eval u) bodyAt0
            requireEqual (eval v) bodyAt1
            -- Body check: extend context with an interval variable
            check (extendCtx i intervalTy ctx) body aTy'
        other -> Left (ExpectedPath other)

-- ─── Glue Element Introduction ────────────────────────────────────────────────
-- Γ ⊢ φ : 𝕀    Γ, φ ⊢ t ⇐ T_e    Γ ⊢ a ⇐ A
-- ──────────────────────────────────────────────
--   Γ ⊢ glue φ t a ⇐ Glue A φ T_e
check ctx (TGlueElem phi t a) ty =
    case eval ty of
        TGlue aTy phi' te -> do
            checkInterval ctx phi
            requireEqual (eval phi') (eval phi)
            check ctx t (eval te)
            check ctx a (eval aTy)
        other -> Left (Other $
            "glue: expected Glue type, got: " ++ show other)

-- ─── Subsumption (switch to inference) ───────────────────────────────────────
-- If we have no special checking rule, infer the type and compare definitionally.
check ctx t ty = do
    ty' <- infer ctx t
    requireEqual (eval ty) (eval ty')
-- ---------------------------------------------------------------------------
-- Top-level helpers
-- ---------------------------------------------------------------------------

-- | Infer the type of a closed term (empty context).
inferClosed :: Term -> Either TypeError Term
inferClosed = infer []

-- | Check a closed term against a type (empty context).
checkClosed :: Term -> Term -> Either TypeError ()
checkClosed t ty = check [] t ty

-- | Pretty-print a type-checking result.
reportInfer :: String -> Term -> IO ()
reportInfer label t =
    case inferClosed t of
        Right ty ->
            putStrLn $ "  ✓  " ++ label ++ "\n       : " ++ show ty
        Left err ->
            putStrLn $ "  ✗  " ++ label ++ "\n" ++ show err

reportCheck :: String -> Term -> Term -> IO ()
reportCheck label t ty =
    case checkClosed t ty of
        Right () ->
            putStrLn $ "  ✓  " ++ label ++ "\n       ⊢ " ++ show t
            ++ "\n       : " ++ show ty
        Left err ->
            putStrLn $ "  ✗  " ++ label ++ "\n" ++ show err
