> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.RunTT where

Representation of the run-time language.
Used for spitting out GHC core.

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.ICompile
> import Ivor.Nobby

When we compile, we need to know the term as well as bits of info about
its type, ie its arity and emptiness.

> type RunValue = (RunTT, TypeInfo)

> data RunTT =
>        RTVar Int -- de Bruijn level
>      | RTFun Name
>      | RTCon Int Name [RunValue] -- Fully applied, Name is for display only
>      | RTElim Name RunValue RunValue [RunValue] -- Fully applied, with
>                               -- target, motive, methods
>      | RTApp RunValue [RunValue]
>      | RTBind (RTBinder,TypeInfo) RunValue 
>      | RTCase Name RunValue [RunValue] -- name is type case is on
>      | RTProj Name Int RunValue -- name is type we're projecting from
>      | forall c. Constant c => RTConst c
>      | RTypeVal -- Useless, uninspectable type value
>      | RTCantHappen -- Flag on unexecutable code
>   -- deriving Show

> data RTBinder = RTLam
>	        | RTPi
>	        | RTLet RunValue
> --  deriving Show

> data TypeInfo = TI Int Bool -- Arity, emptiness (whether its the empty type)
>   deriving Show

> newtype RunTTs = RGam [(Name,RunTT)]

Make a term in RunTT from a de Bruijn levelled representation

> mkRTFun :: Gamma Name -> Levelled Name -> RunTT
> mkRTFun gam (Lev term) = mkrt 0 term where
>    mkrt l (P n) = RTFun n
>    mkrt l (V x) = RTVar x
>    mkrt l (Con t n 0) = RTCon t n []
>    mkrt l c@(Con t n a) = mkApp l c []
>    mkrt l (TyCon n x) = RTypeVal
>    mkrt l (Elim n) = RTFun n
>    mkrt l c@(App f a) = mkApp l c []
>    mkrt l (Bind n b (Sc sc)) = RTBind (mkBinder l b) 
>			            ((mkrt (l+1) sc), TI 0 False)
>    mkrt l (Proj n i t) = RTProj n i (mkrt l t, TI 0 False)
>    mkrt l (Label t _) = mkrt l t
>    mkrt l (Call _ t) = mkrt l t
>    mkrt l (Return t) = mkrt l t
>    mkrt l (Const c) = RTConst c -- error "Sorry, I don't know how to compile constants yet"
>    mkrt l (Stage _) = error "Sorry, I can't compile multi-stage programs."
>    mkrt l Star = RTypeVal

>    mkBinder l (B Lambda t) = (RTLam, TI 0 False)
>    mkBinder l (B (Let v) t) = (RTLet (mkrt l v, TI 0 False), TI 0 False)
>    mkBinder l (B Pi t) = (RTPi, TI 0 False)

>    mkApp l (App f a) sp = mkApp l f ((mkrt l a, TI 0 False):sp)
>    mkApp l (Con t n a) sp | length sp == a = RTCon t n sp
>		            | otherwise = saturate l a (length sp) 
>                                            (RTCon t n sp) (RTCon t n sp)
>    mkApp l x sp = RTApp (mkrt l x, TI (length sp) False) sp

>    saturate lev arity splen acc (RTCon t n sp) -- cached inner constructor
>        | splen == arity = acc
>        | otherwise = let newcon = RTCon t n (sp++[(RTVar lev, TI 0 False)]) in
>            saturate (lev+1) arity (splen+1)
>               (RTBind (RTLam, TI 0 False) (newcon, TI 0 False)) 
>                  newcon
>    

let c = mkRawApp (Con tag naem arity) sp in
                  error $ "Saturate " ++ show c

    mkRawApp = forget mr
      where mr f [] = f
            mr f (x:xs) = mr (App f x) xs


error "Constructor saturation unimplemented"

Make an elimination rule in RunTT from a simple case expression

> mkRTElim :: Name -> Int -> SimpleCase -> RunTT
> mkRTElim ename arity es = fst $ abstract arity (mkrt es)
>    where mkrt Impossible = RTCantHappen
>          mkrt (IReduce t) = mkRTFun (Gam []) (mkvarnum t)
>          mkrt (Case ty x cs) = RTCase ty (RTVar (arity-x-1), TI 0 False)
>		                  (map mkcase cs)
>	   mkcase c = (mkrt c, TI 0 False)
>          mkvarnum (Ind t) = Lev $ vapp (\ (ctx,i) -> V (arity-i-1)) t

>          abstract 0 t = (t, TI 0 False)
>          abstract n t = (RTBind (RTLam, TI 0 False) (abstract (n-1) t), TI 0 False)
