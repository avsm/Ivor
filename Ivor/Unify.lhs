> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Unify where

> import Ivor.Nobby
> import Ivor.TTCore

> import Debug.Trace

> type Unified = [(Name, TT Name)]

Unify on named terms, but normalise using de Bruijn indices.
(I hope this doesn't get too confusing...)

> unify :: Monad m =>
>          Gamma Name -> Indexed Name -> Indexed Name -> m Unified
> unify gam x y = unifyenv gam [] (finalise x) (finalise y)

> unifyenv :: Monad m =>
>             Gamma Name -> Env Name ->
>             Indexed Name -> Indexed Name -> m Unified
> -- For the sake of readability of the results, first attempt to unify
> -- without reducing global names, and reduce if that doesn't work.
> -- (Actually, I'm not sure this helps. Probably just slows things down.)
> unifyenv gam env x y = 
>     case unifynf env (p (normalise emptyGam x))
>                      (p (normalise emptyGam y)) of
>           (Just x) -> return x
>           Nothing -> unifynf env (p (normalise (gam' gam) x))
>                                  (p (normalise (gam' gam) y))
>    where p (Ind t) = Ind (makePs t)
>          gam' g = concatGam g (envToGamHACK env)

Make the local environment something that Nobby knows about. Very hacky...

> envToGamHACK [] = emptyGam
> envToGamHACK ((n,B (Let v) ty):xs)
>     = insertGam n (G (Fun [] (Ind v)) (Ind ty)) (envToGamHACK xs)
> envToGamHACK (_:xs) = envToGamHACK xs

> unifynf :: Monad m => 
>            Env Name -> Indexed Name -> Indexed Name -> m Unified
> unifynf env (Ind x) (Ind y) = un env env x y
>    where un envl envr (P x) (P y) 
>              | x == y = return []
>              | loc x envl == loc y envr && loc x envl >=0
>                  = return []
>          un envl envr (P x) t | hole envl x = return [(x,t)]
>          un envl envr t (P x) | hole envl x = return [(x,t)]
>          un envl envr (Bind x b@(B Hole ty) (Sc sc)) t
>             = un ((x,b):envl) envr sc t
>          un envl envr (Bind x b (Sc sc)) (Bind x' b' (Sc sc')) =
>              do bu <- unb envl envr b b'
>                 scu <- un ((x,b):envl) ((x',b'):envr) sc sc'
>                 combine bu scu
>          un envl envr (App f s) (App f' s') = 
>              do fu <- un envl envr f f'
>                 su <- un envl envr s s'
>                 combine fu su
>          un envl envr (Proj _ i t) (Proj _ i' t')
>             | i == i' = un envl envr t t'
>          un envl envr (Label t c) (Label t' c') = un envl envr t t'
>          un envl envr (Call c t) (Call c' t') = un envl envr t t'
>          un envl envr (Return t) (Return t') = un envl envr t t'
>          un envl envr (Stage x) (Stage y) = unst envl envr x y
>          un envl envr x y 
>                     | x == y = return []
>                     | otherwise = fail $ "Can't unify " ++ show x ++
>                                          " and " ++ show y
>          unb envl envr (B b ty) (B b' ty') = 
>              do bu <- unbb envl envr b b'
>                 tyu <- un envl envr ty ty'
>                 combine bu tyu
>          unbb envl envr Lambda Lambda = return []
>          unbb envl envr Pi Pi = return []
>          unbb envl envr Hole Hole = return []
>          unbb envl envr (Let v) (Let v') = un envl envr v v'
>          unbb envl envr (Guess v) (Guess v') = un envl envr v v'
>          unbb envl envr x y = fail $ "Can't unify "++show x++" and "++show y

>          unst envl envr (Quote x) (Quote y) = un envl envr x y
>          unst envl envr (Code x) (Code y) = un envl envr x y
>          unst envl envr (Eval x _) (Eval y _) = un envl envr x y
>          unst envl envr (Escape x _) (Escape y _) = un envl envr x y
>          unst envl envr x y = fail $ "Can't unify " ++ show (Stage x) ++
>                                      " and " ++ show (Stage y)

>          hole env x | (Just (B Hole ty)) <- lookup x env = True
>                     | otherwise = isInferred x
>          isInferred (MN ("INFER",_)) = True -- OK, a bit of a nasty hack.
>          isInferred _ = False

>          combine [] ys = return ys
>          combine ((n,tm):xs) ys 
>              | (Just tm') <- lookup n ys 
>                  = if (ueq tm tm')  -- Take account of names! == no good.
>                       then do rest <- combine xs ys
>                               return $ (n,tm):rest
>                       else fail $ "Can't unify " ++ show tm ++ 
>                                   " and " ++ show tm'
>              | otherwise = do rest <- combine xs ys
>                               return $ (n,tm):rest
>          loc x xs = loc' 0 x xs
>          loc' i x ((n,_):xs) | x == n = i
>                              | otherwise = loc' (i+1) x xs
>          loc' i x [] = -1

An equality test which takes account of names which should be equal.
TMP HACK! ;)

>          ueq :: TT Name -> TT Name -> Bool
>          ueq x y = case unifyenv (Gam []) [] (Ind x) (Ind y) of
>                   Just [] -> True
>                   _ -> False

Grr!

> ueq :: Gamma Name -> TT Name -> TT Name -> Bool
> ueq gam x y = case unifyenv gam [] (Ind x) (Ind y) of
>                   Just [] -> True
>                   _ -> False


> substNames :: [(Name,TT Name)] -> TT Name -> TT Name
> substNames [] tm = tm
> substNames ((n,t):xs) tm = substNames xs (substName n t (Sc tm))

Look for a specific term (unifying with a subterm)
and replace it.

> unifySubstTerm :: Gamma Name -> TT Name -> TT Name -> 
>                   Scope (TT Name) -> TT Name
> unifySubstTerm gam p tm (Sc x) = p' x where
>     p' x | ueq gam x p = tm
>     p' (App f' a) = (App (p' f') (p' a))
>     p' (Bind n b (Sc sc)) = (Bind n (fmap p' b) (Sc (p' sc)))
>      --   | n == p = (Bind n (fmap p' b) (Sc sc))
>      --   | otherwise 
>     p' (Proj n i x) = Proj n i (p' x)
>     p' (Label t (Comp n cs)) = Label (p' t) (Comp n (map p' cs))
>     p' (Call (Comp n cs) t) = Call (Comp n (map p' cs)) (p' t)
>     p' (Return t) = Return (p' t)
>     p' (Stage (Quote t)) = Stage (Quote (p' t))
>     p' (Stage (Code t)) = Stage (Code (p' t))
>     p' (Stage (Eval t ty)) = Stage (Eval (p' t) (p' ty))
>     p' (Stage (Escape t ty)) = Stage (Escape (p' t) (p' ty))
>     p' x = x

