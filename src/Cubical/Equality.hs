module Cubical.Equality
    ( definitionallyEqual
    , definitionallyEqualCtx
    , etaEq
    , reducePAppByType
    ) where

import Cubical.Interval (I(..))
import Cubical.Syntax
import Cubical.Eval (eval, isTopDNF, isBotDNF)

-- Ctx imported from TypeChecker would create a cycle, so we re-alias here.
-- The full Ctx type lives in TypeChecker; equality only needs the list shape.
type Ctx = [(Name, Term)]

--------------------------------------------------------------------------------
-- Context-free definitional equality
--------------------------------------------------------------------------------

definitionallyEqual :: Term -> Term -> Bool
definitionallyEqual t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in v1 == v2 || etaEq 8 [] v1 v2

definitionallyEqualCtx :: Ctx -> Term -> Term -> Bool
definitionallyEqualCtx ctx t1 t2 =
    let v1 = eval t1; v2 = eval t2
    in v1 == v2 || etaEq 10 ctx v1 v2

--------------------------------------------------------------------------------
-- Path boundary reduction
--------------------------------------------------------------------------------

-- | If p : Path A u v and r is I0/I1, return the endpoint.
reducePAppByType :: Ctx -> Term -> Term -> Maybe Term
reducePAppByType ctx p r =
    case inferTy ctx p of
        Just (TPath _ u v) ->
            let r' = eval r
            in if isBotDNF r' || r' == TInterval I0 then Just (eval u)
               else if isTopDNF r' || r' == TInterval I1 then Just (eval v)
               else Nothing
        _ -> Nothing
  where
    inferTy c (TVar i)
        | i >= 0, i < length c = Just (eval (shift (i+1) 0 (snd (c !! i))))
        | otherwise             = Nothing
    inferTy c (TApp f a) =
        case inferTy c f of
            Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
            _                  -> Nothing
    inferTy _ _ = Nothing

--------------------------------------------------------------------------------
-- Lightweight neutral type inference (used by etaEq for lambda domains)
--------------------------------------------------------------------------------

inferNeutralTy :: Ctx -> Term -> Maybe Term
inferNeutralTy ctx (TVar i)
    | i >= 0, i < length ctx = Just (eval (shift (i+1) 0 (snd (ctx !! i))))
    | otherwise               = Nothing
inferNeutralTy ctx (TApp f a) =
    case inferNeutralTy ctx f of
        Just (TPi _ _ bTy) -> Just (eval (beta bTy a))
        _                  -> Nothing
inferNeutralTy _ _ = Nothing

inferLamDom :: Ctx -> Term -> Term -> Term
inferLamDom ctx (TAbs _ _) neutral =
    case inferNeutralTy ctx neutral of
        Just (TPi _ domTy _) -> eval domTy
        _                    -> TUniv 0
inferLamDom _ _ _ = TUniv 0

--------------------------------------------------------------------------------
-- Core eta-equality
--------------------------------------------------------------------------------

etaEq :: Int -> Ctx -> Term -> Term -> Bool
etaEq 0 _ _ _ = False
etaEq fuel ctx t1 t2
    | t1 == t2 = True

    -- Path boundary reduction
    | PApp p r <- t1, Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx u t2
    | PApp p r <- t2, Just u <- reducePAppByType ctx p r
    = etaEq (fuel-1) ctx t1 u

    -- Lambda eta
    | TAbs x b1 <- t1, TAbs _ b2 <- t2
    = etaEq (fuel-1) ((x, inferLamDom ctx t1 t2) : ctx) (eval b1) (eval b2)
    | TAbs x b2 <- t2
    = let ctx' = (x, inferLamDom ctx t2 t1) : ctx
      in etaEq (fuel-1) ctx' (eval (TApp (shift 1 0 t1) (TVar 0))) (eval b2)
    | TAbs x b1 <- t1
    = let ctx' = (x, inferLamDom ctx t1 t2) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval (TApp (shift 1 0 t2) (TVar 0)))

    -- Path-lambda eta
    | PLam i b1 <- t1, PLam _ b2 <- t2
    = etaEq (fuel-1) ((i, TIntervalTy) : ctx) (eval b1) (eval b2)
    | PLam i b2 <- t2
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval (PApp (shift 1 0 t1) (TVar 0))) (eval b2)
    | PLam i b1 <- t1
    = let ctx' = (i, TIntervalTy) : ctx
      in etaEq (fuel-1) ctx' (eval b1) (eval (PApp (shift 1 0 t2) (TVar 0)))

    -- Congruence on neutral spines
    | TApp f1 a1 <- t1, TApp f2 a2 <- t2
    = etaEq (fuel-1) ctx f1 f2 && etaEq (fuel-1) ctx a1 a2
    | PApp p1 r1 <- t1, PApp p2 r2 <- t2
    = etaEq (fuel-1) ctx p1 p2 && etaEq (fuel-1) ctx r1 r2

    -- Type congruence
    | TPi _ a1 b1 <- t1, TPi _ a2 b2 <- t2
    = etaEq (fuel-1) ctx a1 a2 && etaEq (fuel-1) ctx b1 b2
    | TPath ty1 u1 v1 <- t1, TPath ty2 u2 v2 <- t2
    = etaEq (fuel-1) ctx ty1 ty2
      && etaEq (fuel-1) ctx u1 u2
      && etaEq (fuel-1) ctx v1 v2

    | otherwise = False