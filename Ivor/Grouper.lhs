> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Grouper where

> import Ivor.TTCore
> import Ivor.Nobby
> import Ivor.Constant

TT expressions with lambdas/function arguments grouped, for better lambda
lifting.

> data GroupTT n
>    = GP n
>    | GV Int
>    | GCon Int n [GroupTT n] -- Saturated now
>    | GTyCon n Int
>    | GElim n
>    | GApp (GroupTT n) [GroupTT n]
>    | GLam [GroupTT n] Int (GroupTT n) -- Variables and level
>    | GLet (GroupTT n) (GroupTT n) (GroupTT n)
>    | GPi (GroupTT n) (GroupTT n)
>    | GProj Int (GroupTT n)
>    | forall c. Constant c => GConst c
>    | GStar
>    | GCant
>  -- deriving Show

> group :: Show n => Levelled n -> GroupTT n
> group (Lev term) = gr 0 term where
>    gr l (P n) = GP n
>    gr l (V i) = GV i
>    gr l c@(Con t n a) = mkApp l c []
>    gr l (TyCon n a) = GTyCon n a
>    gr l (Elim n) = GElim n
>    gr l c@(App f a) = mkApp l c []
>    gr l (Bind n (B Lambda t) (Sc sc)) = mkLam (l+1) [gr l t] sc
>    gr l (Bind n (B Pi t) (Sc sc)) = GPi (gr l t) (gr (l+1) sc)
>    gr l (Bind n (B (Let v) t) (Sc sc)) 
>		      = GLet (gr l v) (gr l t) (gr (l+1) sc)
>    gr l (Proj _ i t) = GProj i (gr l t)
>    gr l (Const c) = GConst c
>    gr l (Label t _) = gr l t
>    gr l (Call _ t) = gr l t
>    gr l (Return t) = gr l t
>    gr l Star = GStar
>    gr _ _ = GCant

>    mkApp l (App f a) sp = mkApp l f ((gr l a):sp)
>    mkApp l (Con t n a) sp | length sp == a = GCon t n sp
>		            | otherwise = saturate l t n a sp
>    mkApp l x sp = GApp (gr l x) sp

>    mkLam l xs (Bind n (B Lambda t) (Sc sc)) 
>            = mkLam (l+1) (xs++[gr l t]) sc
>    mkLam l xs sc = GLam xs (l-length xs) (gr l sc)

>    saturate lev tag name arity sp 
>            = error $ "Constructor saturation unimplemented " ++ show term

