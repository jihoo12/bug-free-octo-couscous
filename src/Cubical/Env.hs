module Cubical.Env
    ( GlobalEnv
    , globalCtx
    , applyGlobals
    , inferWithEnv
    , checkWithEnv
    ) where

import Cubical.Syntax (Name, Term(..))
import Cubical.TypeChecker (Ctx, TypeError, infer, check)

--------------------------------------------------------------------------------
-- Global Named Environment
--------------------------------------------------------------------------------

-- | A global definition: (name, type, value).
-- Stored most-recent first.
type GlobalEnv = [(Name, Term, Term)]

-- | Build a Ctx from a GlobalEnv. Variables are ordered innermost-first,
-- so we reverse the env.
globalCtx :: GlobalEnv -> Ctx
globalCtx genv = map (\(n, ty, _) -> (n, ty)) (reverse genv)

-- | Wrap a term so global definitions are in scope as let-bindings.
-- applyGlobals [(x,T,v), ...] t = (λx. t) v, ordered outermost-first.
applyGlobals :: GlobalEnv -> Term -> Term
applyGlobals genv t = foldr wrap t (reverse genv)
  where
    wrap (x, _ty, val) body = TApp (TAbs x body) val

-- | Infer the type of a term in the context of a GlobalEnv.
inferWithEnv :: GlobalEnv -> Term -> Either TypeError Term
inferWithEnv genv t = infer (globalCtx genv) t

-- | Check a term against a type in the context of a GlobalEnv.
checkWithEnv :: GlobalEnv -> Term -> Term -> Either TypeError ()
checkWithEnv genv t ty = check (globalCtx genv) t ty