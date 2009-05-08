> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Evaluator(eval_whnf, eval_nf) where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant
> import Ivor.Nobby
> import Ivor.Typecheck

> import Debug.Trace
> import Data.Typeable

 data Machine = Machine { term :: (TT Name),
                          mstack :: [TT Name],
                          menv :: [(Name, Binder (TT Name))] }

> eval_whnf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_whnf gam (Ind tm) = let res = makePs (evaluate False gam tm)
>                              in finalise (Ind res)

> eval_nf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_nf gam (Ind tm) = let res = makePs (evaluate True gam tm)
>                            in finalise (Ind res)

> type Stack = [TT Name]
> type SEnv = [(Name, TT Name, TT Name)]

> getEnv i env = (\ (_,_,val) -> val) (env!!i)
> sfst (n,_,_) = n

Code			Stack	Env	Result

[[x{global}]]		xs	es	(lookup x), xs, es
[[x{local}]]		xs	es	(es!!x), xs, es
[[f a]]			xs	es	[[f]], a:xs, es
[[\x . e]]		(x:xs)	es	[[e]], xs, (x:es)
[[\x . e]]		[]	es	\x . [[e]], xs, (Lam x: es)
(or leave alone for whnf)
[[let x = t in e]]	xs	es	[[e]], xs, (Let x t: es)

> evaluate :: Bool -> -- under binders? 'False' gives WHNF
>             Gamma Name -> TT Name -> TT Name
> evaluate open gam tm = eval tm [] [] []
>   where
>     eval :: TT Name -> Stack -> SEnv -> [(Name, TT Name)] -> TT Name
>     eval (P x) xs env pats 
>         = case lookup x pats of
>              Nothing -> evalP x (lookupval x gam) xs env pats
>              Just val -> eval val xs env pats
>     eval (V i) xs env pats = if (length env>i) 
>                                then eval (getEnv i env) xs env pats
>                                else unload (V i) xs pats env -- blocked, so unload
>     eval (App f a) xs env pats = eval f ((eval a [] env pats):xs) env pats
>     eval (Bind n (B Lambda ty) (Sc sc)) xs env pats =
>         let ty' = eval ty [] env pats in
>             evalScope n ty' sc xs env pats
>     eval (Bind n (B Pi ty) (Sc sc)) xs env pats =
>         let ty' = eval ty [] env pats in
>            unload (Bind n (B Pi ty') (Sc sc)) [] pats env
>     eval (Bind n (B (Let val) ty) (Sc sc)) xs env pats =
>         eval sc xs ((n,ty,eval val [] env pats):env) pats
>     eval (Bind n (B bt ty) (Sc sc)) xs env pats =
>         let ty' = eval ty [] env pats in
>            unload (Bind n (B bt ty') (Sc sc)) [] pats env
>     eval x stk env pats = unload x stk pats env

>     evalP n (Just v) xs env pats 
>        = case v of
>             Fun opts (Ind v) -> eval v xs env pats
>             PatternDef p _ -> pmatch n p xs env pats
>             PrimOp _ f -> case f xs of
>                             Nothing -> unload (P n) xs pats env
>                             Just v -> eval v [] env pats
>             _ -> unload (P n) xs pats env
>     evalP n Nothing xs env pats = unload (P n) xs pats env -- blocked, so unload stack

>     evalScope n ty sc (x:xs) env pats = eval sc xs ((n,ty,x):env) pats
>     evalScope n ty sc [] env pats
>       | open = let n' = uniqify n (map sfst env)
>                    newsc = pToV n' (eval sc [] ((n',ty,P n'):env) pats) in
>                    buildenv env $ unload (Bind n' (B Lambda ty) newsc)
>                                          [] pats env
>       | otherwise 
>          = buildenv env $ unload (Bind n (B Lambda ty) (Sc sc)) [] pats env -- in Whnf
>     unload x [] pats env 
>                = foldl (\tm (n,val) -> substName n val (Sc tm)) x pats
>     unload x (a:as) pats env = unload (App x a) as pats env

>     buildenv [] t = t
>     buildenv ((n,ty,tm):xs) t 
>                 = buildenv xs (subst tm (Sc t))
>     --            = buildenv xs (Bind n (B (Let tm) ty) (Sc t))

>     pmatch n (PMFun i clauses) xs env pats = 
>         case matches clauses xs env pats of
>           Nothing -> unload (P n) xs pats env
>           Just (rhs, pbinds, stk) -> eval rhs stk env pbinds

>     matches [] xs env pats = Nothing
>     matches (c:cs) xs env pats 
>        = case (match c xs env pats) of
>            Just v -> Just v
>            Nothing -> matches cs xs env pats

>     match :: Scheme Name -> [TT Name] -> SEnv -> [(Name, TT Name)] ->
>              Maybe (TT Name, [(Name, TT Name)], Stack)
>     match (Sch pats rhs) xs env patvars 
>               = matchargs pats xs rhs env patvars
>     matchargs [] xs (Ind rhs) env patvars = Just (rhs, patvars, xs)
>     matchargs (p:ps) (x:xs) rhs env patvars
>               = case matchPat p (eval x [] env patvars) patvars of
>                   Just patvars' -> matchargs ps xs rhs env patvars'
>                   Nothing -> Nothing
>     matchargs _ _ _ _ _ = Nothing

>     matchPat PTerm x patvars = Just patvars
>     matchPat (PVar n) x patvars = Just ((n,x):patvars)
>     matchPat (PConst t) (Const t') patvars
>                  = do tc <- cast t
>                       if (tc == t') then Just patvars
>                                else Nothing
>     matchPat pc@(PCon t _ _ args) app patvars
>              | Just (tag, cargs) <- getConArgs app [] =
>                     if (tag == t) then matchPats args cargs patvars
>                        else Nothing
>         where matchPats [] [] patvars = Just patvars
>               matchPats (a:as) (b:bs) patvars
>                   = do vs' <- matchPat a b patvars
>                        matchPats as bs vs'
>               matchPats _ _ _ = Nothing
>     matchPat _ _ _ = Nothing

>     getConArgs (Con t _ _) args = Just (t, args)
>     getConArgs (App f a) args = getConArgs f (a:args)
>     getConArgs _ _ = Nothing
