module Cubical.Eval
    ( eval
    , equivDom
    , isTopDNF, isBotDNF
    ) where

import Cubical.Interval (dnfTop, dnfBot, evalInterval, I(..))
import Cubical.Syntax

--------------------------------------------------------------------------------
-- DNF Helpers
--------------------------------------------------------------------------------

isTopDNF :: Term -> Bool
isTopDNF (TCube d) = d == dnfTop
isTopDNF _         = False

isBotDNF :: Term -> Bool
isBotDNF (TCube d) = d == dnfBot
isBotDNF _         = False

--------------------------------------------------------------------------------
-- Evaluator
--------------------------------------------------------------------------------

-- Forward declaration: definitionallyEqual lives in Equality, but eval needs
-- it for the transport trivial-path check. We break the cycle by inlining a
-- syntactic structural equality here (eval-time only; no eta).
syntacticEq :: Term -> Term -> Bool
syntacticEq = (==)

eval :: Term -> Term
eval t = case t of
    TApp f a ->
        case eval f of
            TAbs _ body -> eval (beta body (eval a))
            f'          -> TApp f' (eval a)

    PApp p r ->
        let r' = eval r
        in case eval p of
            PLam _ body -> eval (beta body r')
            p'          -> PApp p' r'

    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TPath a u v -> TPath (eval a) (eval u) (eval v)
    PLam i b    -> PLam i (eval b)
    TInterval i -> TCube (evalInterval i)

    THComp aTy phi tube base ->
        let phi' = eval phi
        in if isTopDNF phi'
           then case eval tube of
                    PLam _ body -> eval (beta body (TInterval I1))
                    tube'       -> PApp tube' (TInterval I1)
           else if isBotDNF phi'
           then eval base
           else THComp (eval aTy) phi' (eval tube) (eval base)

    TEquiv a b ->
        TEquiv (eval a) (eval b)

    TMkEquiv a b f g eta eps ->
        TMkEquiv (eval a) (eval b) (eval f) (eval g) (eval eta) (eval eps)

    TEquivFwd e x ->
        let e' = eval e; x' = eval x
        in case e' of
            TMkEquiv _ _ f _ _ _ -> eval (TApp f x')
            _                    -> TEquivFwd e' x'

    TUa e -> TUa (eval e)

    TTransport p x ->
        let p' = eval p; x' = eval x
        in case p' of
            TUa e -> eval (TEquivFwd e x')
            PLam iName body ->
                let b0 = eval (beta body (TInterval I0))
                    b1 = eval (beta body (TInterval I1))
                in if syntacticEq b0 b1
                   then x'
                   else case (b0, b1) of
                       (TPi argName _ _, TPi _ _ _) ->
                           TAbs argName $
                               let fa = TApp (shift 1 0 x') (TVar 0)
                               in eval (TTransport
                                           (PLam iName
                                               (eval (TApp (beta (shift 2 0 body)
                                                               (TInterval I1))
                                                           (shift 2 0 (TVar 0)))))
                                           fa)
                       _ -> TTransport p' x'
            _ -> TTransport p' x'

    TGlue aTy phi te ->
        let phi' = eval phi
        in if isTopDNF phi'
           then equivDom (eval te)
           else if isBotDNF phi'
           then eval aTy
           else TGlue (eval aTy) phi' (eval te)

    TGlueElem phi t a ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval t
           else if isBotDNF phi'
           then eval a
           else TGlueElem phi' (eval t) (eval a)

    TUnglue phi te g ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval (TEquivFwd (eval te) (eval g))
           else if isBotDNF phi'
           then eval g
           else TUnglue phi' (eval te) (eval g)

    _ -> t

-- | Extract the domain type from an equivalence term.
equivDom :: Term -> Term
equivDom (TMkEquiv a _ _ _ _ _) = a
equivDom (TEquiv a _)           = a
equivDom other                  = other