> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.MakeData where

> import Ivor.TTCore
> import Ivor.Datatype

> import Debug.Trace

Transform a raw data declaration (just parameters and constructors)
into a full data definition with iota schemes.

FIXME: Throughout all this, need to ensure that the elimination operator name,
the target, methods and the motives are unique.

> type Params = [(Name,Raw)]
> type Constructors = [(Name,Raw)]

> mkRawData :: Monad m =>
>              Name -> Params -> Raw -> Constructors -> m RawDatatype
> mkRawData name params contype cons = 
>     let ecasetype = mkCaseType True name params contype cons 
>                                motiveName methNames
>         ccasetype = mkCaseType False name params contype cons 
>                                motiveName methNames
>         datacons = mkDatacons params cons
>         eischemes = mkSchemes True name (ruleName name "Elim") 
>                               params datacons motiveName methNames
>         cischemes = mkSchemes False name (ruleName name "Case") 
>                               params datacons motiveName methNames
>         tycontype = mkCon params contype in
>         return $ RData (name,tycontype) datacons (length params)
>                    (ruleName name "Elim", ecasetype) -- elim rule
>                    (ruleName name "Case", ccasetype) -- case rule
>                    eischemes -- elim rule iota schemes
>                    cischemes -- case rule iota schemes

>    where ruleName (UN n) suff = (UN (n++suff)) -- TMP HACK!
>          motiveName = (UN "Phi")
>          methName (UN n) = (UN ("meth_"++n))
>          methNames = map (methName.fst) cons
 
> mkSchemes :: Bool -> Name -> Name -> Params -> Constructors -> Name -> 
>              [Name] -> [RawScheme]
> mkSchemes rec n ername ps cs motive mns = mks cs mns mns 
>    where mks [] [] mns = [] 
>          mks ((c,cty):cs) (m:ms) mns 
>              = (mkScheme rec n ername ps c cty motive mns m):(mks cs ms mns)

> mkScheme rec n ername ps c cty motive mns meth 
>     = RSch (mkIArgs ps c cty motive mns)
>            (RWRet (mkIRet rec n ername meth motive mns ps cty))

> mkIArgs ps c cty motive mns = getappargs (getrettype cty) ++
>                               [mkapp (Var c) (map Var (getargnames cty))] ++
>                               (map Var (motive:mns))

> mkIRet rec tyname ername meth motive mns ps cty = 
>     mkapp (Var meth) (drop (length ps) (mkArgs cty))
>   where mkArgs (RBind n (B Pi ty) sc) 
>            | isrec ty tyname && rec 
>                = (Var n):(mkRecApp ername ty n motive mns):(mkArgs sc)
>            | otherwise = (Var n):(mkArgs sc)
>         mkArgs (RFileLoc f l t) = mkArgs t
>         mkArgs _ = []
>         mkRecApp en ty n motive mns = 
>             mkapp (Var en) $ (getappargs ty)++(map Var (n:motive:mns))


> mkCon :: Params -> Raw -> Raw
> mkCon [] ty = ty
> mkCon ((x,xty):xs) ty = RBind x (B Pi xty) (mkCon xs ty)

> mkDatacons :: Params -> Constructors -> Constructors
> mkDatacons _ [] = []
> mkDatacons ps ((x,xty):xs) = (x,(mkCon ps xty)):(mkDatacons ps xs)

> mkCaseType :: Bool -> Name -> Params -> Raw -> Constructors -> Name -> 
>               [Name] -> Raw
> mkCaseType rec n ps ty cs motiveName mns 
>     = bindParams ps $
>       bindIndices ty $
>       bindTarget targetName n ps ty $
>       bindMotive motiveName targetName n ps ty $
>       bindMethods rec n motiveName ps cs mns $
>       applyMethod motiveName targetName ty
>    where targetName = UN "target" -- TMP HACK!

> bindParams [] rest = rest
> bindParams ((n,ty):xs) rest = RBind n (B Pi ty) (bindParams xs rest)

> bindIndices (RBind n (B Pi ty) sc) rest 
>     = (RBind n (B Pi ty) (bindIndices sc rest))
> bindIndices (RFileLoc f l t) rest = bindIndices t rest
> bindIndices sc rest = rest

> bindTarget x n ps ty rest 
>     = RBind x 
>       (B Pi (mkapp (Var n) (map Var ((map fst ps)++(getargnames ty)))))
>       rest

> bindMotive p x n ps ty rest
>     = RBind p
>       (B Pi (bindIndices ty $
>              bindTarget x n ps ty $
>              RStar)) rest

> bindMethods rec tyname p ps [] [] rest = rest
> bindMethods rec tyname p ps ((n,ty):cs) (mn:mns) rest 
>     = RBind mn (B Pi (methtype ty)) (bindMethods rec tyname p ps cs mns rest)
>  where methtype (RBind a (B Pi argtype) sc) 
>            | isrec argtype tyname && rec
>                = (RBind a (B Pi argtype) (mkrec a argtype sc))
>            | otherwise = (RBind a (B Pi argtype) (methtype sc))
>        methtype (RFileLoc _ _ t) = methtype t
>        methtype sc = mkapp (Var p) $ (getindices sc)++
>              [mkapp (Var n) (map Var ((map fst ps)++(getargnames ty)))]
>        mkrec a argtype sc = (RBind (ih a) (B Pi (rectype a argtype p)) 
>                                        (methtype sc))
>        getindices x = drop (length ps) (getappargs x)
>        ih (UN a) = UN (a++"_IH")
>        rectype a aty p = mkapp (Var p) ((drop (length ps) (getappargs aty)++[Var a]))

> applyMethod p x ty = mkapp (Var p) ((map Var (getargnames ty)) ++ [Var x])


> isrec t tyname = (Var tyname) == getappfun t

> placeholder = Var (UN "Waitforit")

