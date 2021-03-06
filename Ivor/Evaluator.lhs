> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Evaluator(eval_whnf, eval_nf, eval_nf_env,
>                       eval_nf_without, eval_nf_limit,
>                       eval_nfEnv, tidyNames) where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant
> import Ivor.Values

> import Debug.Trace
> import Data.Typeable
> import Control.Monad.State
> import List
> import qualified Data.Map as Map

 data Machine = Machine { term :: (TT Name),
                          mstack :: [TT Name],
                          menv :: [(Name, Binder (TT Name))] }

> eval_whnf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_whnf gam (Ind tm) = let res = makePs (evaluate False gam tm Nothing Nothing Nothing)
>                              in finalise (Ind res)

> eval_nf :: Gamma Name -> Indexed Name -> Indexed Name
> eval_nf gam (Ind tm) = let res = makePs (evaluate True gam tm Nothing Nothing Nothing)
>                            in finalise (Ind res)

> eval_nf_env :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> eval_nf_env env g t
>     = eval_nf (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g)
>             = addenv xs (Gam (Map.insert n (G (Fun [] (Ind v)) (Ind ty) defplicit) g))
>         addenv (_:xs) g = addenv xs g

> eval_nf_without :: Gamma Name -> Indexed Name -> [Name] -> Indexed Name
> eval_nf_without gam tm [] = eval_nf gam tm
> eval_nf_without gam (Ind tm) ns = let res = makePs (evaluate True gam tm (Just ns) Nothing Nothing)
>                                       in finalise (Ind res)

> eval_nf_limit :: Gamma Name -> Indexed Name -> [(Name, Int)] -> 
>                  Maybe [(Name, ([Int], Int))] -> Indexed Name
> eval_nf_limit gam tm [] stat = eval_nf gam tm
> eval_nf_limit gam (Ind tm) ns stat 
>     = let res = makePs (evaluate True gam tm Nothing (Just ns) stat)
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

> type EvalState = (Maybe [(Name, Int)], Maybe [(Name, ([Int], Int))])

> evaluate :: Bool -> -- under binders? 'False' gives WHNF
>             Gamma Name -> TT Name -> 
>             Maybe [Name] ->  -- Names not to reduce
>             Maybe [(Name, Int)] -> -- Names to reduce a maximum number
>             Maybe [(Name, ([Int], Int))] -> -- Names and list of static args
>             TT Name
> evaluate open gam tm jns maxns statics = -- trace ("EVALUATING: " ++ debugTT tm) $ 
>                                  let res = evalState (eval tm [] [] []) (maxns, statics)
>                                      in {- trace ("RESULT: " ++ debugTT res) -} 
>                                         res
>   where
>     eval :: TT Name -> Stack -> SEnv -> 
>             [(Name, TT Name)] -> State EvalState (TT Name)
>     eval tm stk env pats = {- trace (show (tm, stk, env, pats)) $ -} eval' tm stk env pats

>     eval' (P x) xs env pats 
>         = do (mns, sts) <- get
>              let (use, mns', sts') = usename x jns mns (sts, (xs, pats))
>              put (mns', sts)
>              case lookup x pats of
>                 Nothing -> if use then evalP x (lookupval x gam) xs env pats
>                                   else evalP x Nothing xs env pats
>                 Just val -> eval val xs env (removep x pats)
>        where removep n [] = []
>              removep n ((x,t):xs) | n==x = removep n xs
>                                   | otherwise = (x,t):(removep n xs)
>     eval' (V i) xs env pats 
>              = if (length env>i) 
>                   then eval (getEnv i env) xs env pats
>                   else unload (V i) xs pats env -- blocked, so unload
>     eval' (App f a) xs env pats 
>        = do a' <- eval a [] env pats
>             eval f (a':xs) env pats
>     eval' (Bind n (B Lambda ty) (Sc sc)) xs env pats
>        = do ty' <- eval ty [] env pats
>             evalScope Lambda n ty' sc xs env pats
>     eval' (Bind n (B Pi ty) (Sc sc)) xs env pats
>        = do ty' <- eval ty [] env pats
>             evalScope Pi n ty' sc xs env pats
>            -- unload (Bind n (B Pi ty') (Sc sc)) [] pats env
>     eval' (Bind n (B (Let val) ty) (Sc sc)) xs env pats 
>        = do val' <- eval val [] env pats
>             eval sc xs ((n,ty,val'):env) pats
>     eval' (Bind n (B bt ty) (Sc sc)) xs env pats
>        = do ty' <- eval ty [] env pats
>             unload (Bind n (B bt ty') (Sc sc)) [] pats env
>     eval' x stk env pats = unload x stk pats env

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

     usename x _ mns (sts, (stk, pats)) 
          | Just (static, arity) <- lookup x sts 
              = useDyn x mns static arity stk pats

>     usename x Nothing Nothing (sts, _) = (True, Nothing, sts)
>     usename x _ (Just ys) (sts, _) 
>                 = case lookup x ys of
>                      Just 0 -> (False, Just ys, sts)
>                      Just n -> (True, Just (update x (n-1) ys), sts)
>                      _ -> (True, Just ys, sts)
>     usename x (Just xs) m (sts, _) = (not (elem x xs), m, sts)

     useDyn x mns static arity stk pats =

>     update x v [] = []
>     update x v ((k,_):xs) | x == k = ((x,v):xs)
>     update x v (kv:xs) = kv : update x v xs

>     buildenv [] t = t
>     buildenv ((n,ty,tm):xs) t 
>                 = buildenv xs (subst tm (Sc t))
>     --            = buildenv xs (Bind n (B (Let tm) ty) (Sc t))

>     renameRHS pbinds rhs env = rrhs [] [] (nub pbinds) rhs where
>       rrhs namemap pbinds' [] rhs = {-trace ("BEFORE " ++ show (rhs, pbinds, pbinds')) $ -}
>                                     (pbinds', substNames namemap rhs)
>       rrhs namemap pbinds ((n,t):ns) rhs
>          = let n' = uniqify' (UN (show n)) (map sfst env ++ map fst pbinds ++ map fst ns) in
>                rrhs ((n,P n'):namemap) ((n',t):pbinds) ns rhs

>     substNames [] rhs = {-trace ("AFTER " ++ show rhs) $ -} rhs
>     substNames ((n,t):ns) rhs = substNames ns (substName n t (Sc rhs))

>     pmatch n (PMFun i clauses) xs env pats = 
>         do cm <- matches clauses xs env pats
>            case cm of
>              Nothing -> unload (P n) xs pats env
>              Just (rhs, pbinds, stk) -> 
>                    let (pbinds', rhs') = renameRHS pbinds rhs env in
>                        eval rhs' stk env pbinds'

>     matches [] xs env pats = return Nothing
>     matches (c:cs) xs env pats 
>        = do cm <- (match c xs env pats)
>             case cm of
>               Just v -> return $ Just v
>               Nothing -> matches cs xs env pats

>     match :: Scheme Name -> [TT Name] -> SEnv -> 
>              [(Name, TT Name)] ->
>              State EvalState (Maybe (TT Name, [(Name, TT Name)], Stack))
>     match (Sch pats _ rhs) xs env patvars 
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



> eval_nfEnv :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> eval_nfEnv env g t
>     = eval_nf (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g)
>             = addenv xs (Gam (Map.insert n (G (Fun [] (Ind v)) (Ind ty) defplicit) g))
>         addenv (_:xs) g = addenv xs g

Turn MN to UN, if they are unique, so that they look nicer.

> tidyNames :: Indexed Name -> Indexed Name
> tidyNames (Ind tm) = Ind (tidy' [] tm)
>   where tidy' ns (Bind (MN (n,i)) (B b t) (Sc tm)) = 
>             let n' = uniqify (UN n) ns in
>                 Bind n' (B b (tidy' ns t)) (Sc (tidy' (n':ns) tm))
>         tidy' ns (Bind x (B b t) (Sc tm)) 
>               = Bind x (B b (tidy' ns t)) (Sc (tidy' (x:ns) tm))
>         tidy' ns (App f a) = App (tidy' ns f) (tidy' ns a)
>         tidy' ns x = x
