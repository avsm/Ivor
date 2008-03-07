> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Evaluator(eval_whnf) where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant
> import Ivor.Nobby

> import Debug.Trace
> import Data.Typeable

 data Machine = Machine { term :: (TT Name),
                          mstack :: [TT Name],
                          menv :: [(Name, Binder (TT Name))] }

> eval_whnf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_whnf gam (Ind tm) = Ind (evaluate False gam tm)

> type Stack = [TT Name]
> type SEnv = [TT Name]

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
>                                then eval (env!!i) xs env pats
>                                else unload (V i) xs -- blocked, so unload
>     eval (App f a) xs env pats = eval f ((eval a [] env pats):xs) env pats
>     eval (Bind n (B Lambda ty) (Sc sc)) xs env pats =
>         let ty' = eval ty xs env pats in
>             evalScope n ty' sc xs env pats
>     eval (Bind n (B Pi ty) (Sc sc)) xs env pats =
>         let ty' = eval ty xs env pats in
>            (Bind n (B Pi ty') (Sc sc))
>     eval (Bind n (B (Let val) ty) (Sc sc)) xs env pats =
>         eval sc xs ((eval val [] env pats):env) pats
>     eval (Bind n (B bt ty) (Sc sc)) xs env pats =
>         let ty' = eval ty xs env pats in
>            (Bind n (B bt ty') (Sc sc))
>     eval x stk _ _ = unload x stk

>     evalP n (Just v) xs env pats 
>        = case v of
>             Fun opts (Ind v) -> eval v xs env pats
>             PatternDef p -> pmatch n p xs env pats
>             _ -> unload (P n) xs
>     evalP n Nothing xs env pats = unload (P n) xs -- blocked, so unload stack

>     evalScope n ty sc (x:xs) env pats = eval sc xs (x:env) pats
>     evalScope n ty sc [] env pats
>               | open = error "Normalising not implemented"
>               | otherwise = Bind n (B Lambda ty) (Sc sc) -- in Whnf
>     unload x [] = x
>     unload x (a:as) = unload (App x a) as

>     pmatch n (PMFun i clauses) xs env pats =
>         case matches clauses xs env pats of
>           Nothing -> unload (P n) xs
>           Just (rhs, pbinds) -> eval rhs (drop i xs) env pbinds

>     matches [] xs env pats = Nothing
>     matches (c:cs) xs env pats 
>        = case (match c xs env pats) of
>            Just v -> Just v
>            Nothing -> matches cs xs env pats

>     match :: Scheme Name -> [TT Name] -> SEnv -> [(Name, TT Name)] ->
>              Maybe (TT Name, [(Name, TT Name)])
>     match (Sch pats rhs) xs env patvars 
>               = matchargs pats xs rhs env patvars
>     matchargs [] [] (Ind rhs) env patvars = Just (rhs, patvars)
>     matchargs (p:ps) (x:xs) rhs env patvars
>               = case matchPat p x patvars of
>                   Just patvars' -> matchargs ps xs rhs env patvars'
>                   Nothing -> Nothing

>     matchPat (PVar n) x patvars = Just ((n,x):patvars)
>     matchPat (PConst t) (Const t') patvars
>                  = do tc <- cast t
>                       if (tc == t') then Just patvars
>                                else Nothing
>     matchPat pc@(PCon t _ _ args) app patvars
>              | Just (tag, cargs) <- getConArgs app [] =
>                     if (tag == t) then trace (show (pc, app)) $ matchPats args cargs patvars
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