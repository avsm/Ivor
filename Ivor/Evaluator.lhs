> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Evaluator(eval_whnf, eval_nf, eval_nf_without, eval_nf_limit) where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant
> import Ivor.Nobby
> import Ivor.Typecheck

> import Debug.Trace
> import Data.Typeable
> import Control.Monad.State

 data Machine = Machine { term :: (TT Name),
                          mstack :: [TT Name],
                          menv :: [(Name, Binder (TT Name))] }

> eval_whnf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_whnf gam (Ind tm) = let res = makePs (evaluate False gam tm Nothing Nothing)
>                              in finalise (Ind res)

> eval_nf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_nf gam (Ind tm) = let res = makePs (evaluate True gam tm Nothing Nothing)
>                            in finalise (Ind res)

> eval_nf_without :: Gamma Name -> Indexed Name -> [Name] -> Indexed Name
> eval_nf_without gam tm [] = eval_nf gam tm
> eval_nf_without gam (Ind tm) ns = let res = makePs (evaluate True gam tm (Just ns) Nothing)
>                                       in finalise (Ind res)

> eval_nf_limit :: Gamma Name -> Indexed Name -> [(Name, Int)] -> Indexed Name
> eval_nf_limit gam tm [] = eval_nf gam tm
> eval_nf_limit gam (Ind tm) ns 
>     = let res = makePs (evaluate True gam tm Nothing (Just ns))
>           in finalise (Ind res)

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
>             Gamma Name -> TT Name -> 
>             Maybe [Name] ->  -- Names not to reduce
>             Maybe [(Name, Int)] -> -- Names to reduce a maximum number
>             TT Name
> evaluate open gam tm jns maxns = evalState (eval tm [] [] []) maxns
>   where
>     eval :: TT Name -> Stack -> SEnv -> 
>             [(Name, TT Name)] -> State (Maybe [(Name, Int)]) (TT Name)
>     eval (P x) xs env pats 
>         = do mns <- get
>              let (use, mns') = usename x jns mns
>              put mns'
>              case lookup x pats of
>                 Nothing -> if use then evalP x (lookupval x gam) xs env pats
>                                   else evalP x Nothing xs env pats
>                 Just val -> eval val xs env pats
>     eval (V i) xs env pats 
>              = if (length env>i) 
>                   then eval (getEnv i env) xs env pats
>                   else unload (V i) xs pats env -- blocked, so unload
>     eval (App f a) xs env pats 
>        = do a' <- eval a [] env pats
>             eval f (a':xs) env pats
>     eval (Bind n (B Lambda ty) (Sc sc)) xs env pats
>        = do ty' <- eval ty [] env pats
>             evalScope Lambda n ty' sc xs env pats
>     eval (Bind n (B Pi ty) (Sc sc)) xs env pats
>        = do ty' <- eval ty [] env pats
>             evalScope Pi n ty' sc xs env pats
>            -- unload (Bind n (B Pi ty') (Sc sc)) [] pats env
>     eval (Bind n (B (Let val) ty) (Sc sc)) xs env pats 
>        = do val' <- eval val [] env pats
>             eval sc xs ((n,ty,val'):env) pats
>     eval (Bind n (B bt ty) (Sc sc)) xs env pats
>        = do ty' <- eval ty [] env pats
>             unload (Bind n (B bt ty') (Sc sc)) [] pats env
>     eval x stk env pats = unload x stk pats env

>     evalP n (Just v) xs env pats 
>        = case v of
>             Fun opts (Ind v) -> eval v xs env pats
>             PatternDef p _ _ -> pmatch n p xs env pats
>             PrimOp _ f -> case f xs of
>                             Nothing -> unload (P n) xs pats env
>                             Just v -> eval v [] env pats
>             _ -> unload (P n) xs pats env
>     evalP n Nothing xs env pats = unload (P n) xs pats env -- blocked, so unload stack

>     evalScope b n ty sc (x:xs) env pats = eval sc xs ((n,ty,x):env) pats
>     evalScope b n ty sc [] env pats
>       | open = do let n' = uniqify' n (map sfst env ++ map fst pats)
>                   let  tmpname = (MN ("E", length env))
>                   sc' <- eval sc [] ((n',ty,P tmpname):env) pats
>                   let newsc = pToV tmpname sc'
>                   u' <- unload (Bind n' (B b ty) newsc) [] pats env
>                   return $ buildenv env u'
>       | otherwise 
>          = do let n' = uniqify' n (map sfst env ++ map fst pats)
>               u' <-  unload (Bind n' (B Lambda ty) (Sc sc)) [] pats env -- in Whnf
>               return $ buildenv env u'
>     unload x [] pats env 
>                = return $ foldl (\tm (n,val) -> substName n val (Sc tm)) x pats
>     unload x (a:as) pats env = unload (App x a) as pats env
>
>     uniqify' u@(UN n) ns = uniqify (MN (n,0)) ns
>     uniqify' n ns = uniqify n ns

>     usename x Nothing Nothing = (True, Nothing)
>     usename x _ (Just ys) = case lookup x ys of
>                               Just 0 -> (False, Just ys)
>                               Just n -> (True, Just (update x (n-1) ys))
>                               _ -> (True, Just ys)
>     usename x (Just xs) m = (not (elem x xs), m)

>     update x v [] = []
>     update x v ((k,_):xs) | x == k = ((x,v):xs)
>     update x v (kv:xs) = kv : update x v xs

>     buildenv [] t = t
>     buildenv ((n,ty,tm):xs) t 
>                 = buildenv xs (subst tm (Sc t))
>     --            = buildenv xs (Bind n (B (Let tm) ty) (Sc t))

>     pmatch n (PMFun i clauses) xs env pats = 
>         do cm <- matches clauses xs env pats
>            case cm of
>              Nothing -> unload (P n) xs pats env
>              Just (rhs, pbinds, stk) -> eval rhs stk env pbinds

>     matches [] xs env pats = return Nothing
>     matches (c:cs) xs env pats 
>        = do cm <- (match c xs env pats)
>             case cm of
>               Just v -> return $ Just v
>               Nothing -> matches cs xs env pats

>     match :: Scheme Name -> [TT Name] -> SEnv -> 
>              [(Name, TT Name)] ->
>              State (Maybe [(Name, Int)]) (Maybe (TT Name, [(Name, TT Name)], Stack))
>     match (Sch pats rhs) xs env patvars 
>               = matchargs pats xs rhs env patvars []
>     matchargs [] xs (Ind rhs) env patvars pv' = return $ Just (rhs, pv', xs)
>     matchargs (p:ps) (x:xs) rhs env patvars pv'
>               = do x' <- (eval x [] env patvars) 
>                    case matchPat p x' pv' of
>                      Just patvars' -> matchargs ps xs rhs env patvars patvars'
>                      Nothing -> return Nothing
>     matchargs _ _ _ _ _ _ = return Nothing

>     matchPat PTerm x patvars = Just patvars
>     matchPat (PVar n) x patvars = Just ((n,x):patvars) -- (filter (\ (x,y) -> x/=n) patvars))
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
