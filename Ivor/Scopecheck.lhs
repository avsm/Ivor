> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Scopecheck(scopeCheck) where

> import Ivor.TTCore
> import Ivor.Nobby
> import Ivor.Typecheck
> import Ivor.Values

Typechecking on terms we assume to be okay - in other words, just convert 
bound names to a de Bruijn index.

> scopeCheck :: Gamma Name -> Env Name -> Raw -> TT Name
> scopeCheck gam = sc where
>     sc :: Env Name -> Raw -> TT Name
>     sc env (Var n) =
>         case lookup n env of
>           Just _ -> P n
>           Nothing -> case glookup n gam of
>              Just ((DCon tag i), _) -> Con tag n i
>              Just ((TCon i _),_) -> TyCon n i
>              _ -> P n
>     sc env (RApp f a) = App (sc env f) (sc env a)
>     sc env (RConst c) = Const c
>     sc env (RBind n b scope) =
>         let b' = scBinder env b
>             sc' = sc ((n,b'):env) scope in
>             Bind n b' (pToV n sc')
>     sc env RStar = Star
>     sc env RInfer = error "Can't fastcheck a term with placeholders"
>     sc env t = error $ "Can't fastcheck " ++ show t

>     scBinder :: Env Name -> Binder Raw -> Binder (TT Name)
>     scBinder env (B (Let v) t) 
>                = let v' = sc env v
>                      t' = sc env t in
>                      B (Let v') t'
>     scBinder env (B Lambda t) 
>                = let t' = sc env t in
>                      B Lambda t'
>     scBinder env (B Pi t) 
>                = let t' = sc env t in
>                      B Pi t'
>     scBinder env (B (Guess v) t) 
>                  = error "Can't fastcheck a term with guesses"
>     scBinder env (B (Pattern v) t) 
>                  = error "Can't fastcheck a term with patterns"
>     scBinder env (B MatchAny t) 
>                  = error "Can't fastcheck a term with patterns"
>     scBinder env (B Hole t) 
>                  = error "Can't fastcheck a term with holes"


