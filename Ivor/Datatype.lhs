> module Ivor.Datatype where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Typecheck
> import Ivor.Nobby
> import Ivor.PatternDefs
> import Ivor.Errors

> import Debug.Trace

> data Datadecl = Datadecl {
>                           datatycon :: Name,
>                           params :: [(Name,Raw)],
>                           tycontype :: Raw,
>                           constructors :: [(Name,Raw)]
>                          }

Elaborated version with elimination rule and iota schemes.

> data RawDatatype = 
>	   RData { rtycon :: (Name,Raw),
>	           rdatacons :: [(Name,Raw)],
>                  rnum_params :: Int,
>	           rerule :: (Name,Raw),
>                  rcrule :: (Name,Raw),
>	           re_ischemes :: [RawScheme],
>	           rc_ischemes :: [RawScheme]
>	   }
>   deriving Show

> data Datatype n =
>	   Data { tycon :: (n, Gval n),
>	          datacons :: [(n, Gval n)],
>                 num_params :: Int,
>	          erule :: (n, Indexed n),
>                 crule :: (n, Indexed n),
>	          e_ischemes :: Maybe (PMFun Name),
>	          c_ischemes :: Maybe (PMFun Name),
>	          e_rawschemes :: [RawScheme],
>	          c_rawschemes :: [RawScheme]
>	        }
>       deriving Show

> getPat (Sch p i) = p
> getRed (Sch p i) = i

> getArity [] = 2 -- empty data type should have elim rule of arity 2!
>                 -- (actually not if they're dependent. Fix this.)
> getArity ss = length (getPat (ss!!0))

checkType checks a raw data type, with its elimination rule and iota
schemes, and returns a DataType, ready for compilation to entries in
the context and an executable elimination rule.

> checkType :: Gamma Name -> RawDatatype -> IvorM (Datatype Name)
> checkType gamma (RData (ty,kind) cons numps (er,erty) (cr,crty) eschemes cschemes) = 
>     do (kv, _) <- typecheck gamma kind
>        let erdata = Elims er cr (map fst cons)
>	 let gamma' = extend gamma (ty,G (TCon (arity gamma kv) erdata) kv defplicit)
>	 (consv,gamma'') <- checkCons gamma' 0 cons
>	 (ev, _) <- typecheck gamma'' erty
>	 (cv, _) <- typecheck gamma'' crty
>	 -- let gamma''' = extend gamma'' (er,G (ElimRule dummyRule) ev defplicit)
>        ([(_, esch, _)], _, _) <- checkDef gamma'' er erty eschemes False False
>        ([(_, csch, _)], _, _) <- checkDef gamma'' cr crty cschemes False False
>	 return (Data (ty,G (TCon (arity gamma kv) erdata) kv defplicit) consv numps
>                    (er,ev) (cr,cv) (Just esch) (Just csch) eschemes cschemes)

> checkTypeNoElim :: Gamma Name -> RawDatatype -> IvorM (Datatype Name)
> checkTypeNoElim gamma (RData (ty,kind) cons numps (er,erty) (cr,crty) eschemes cschemes) = 
>     do (kv, _) <- typecheck gamma kind
>        let erdata = Elims er cr (map fst cons)
>	 let gamma' = extend gamma (ty,G (TCon (arity gamma kv) erdata) kv defplicit)
>	 (consv,gamma'') <- checkCons gamma' 0 cons
>	 (ev, _) <- typecheck gamma'' erty
>	 (cv, _) <- typecheck gamma'' crty
>	 -- let gamma''' = extend gamma'' (er,G (ElimRule dummyRule) ev defplicit)
>	 return (Data (ty,G (TCon (arity gamma kv) erdata) kv defplicit) consv numps
>                    (er,ev) (cr,cv) Nothing Nothing [] [])

> checkCons gamma t [] = return ([], gamma)
> checkCons gamma t ((cn,cty):cs) = 
>              do (cv,_) <- typecheck gamma cty
>		  let ccon = G (DCon t (arity gamma cv)) cv defplicit
>		  let gamma' = extend gamma (cn,ccon)
>		  (rest,gamma'') <- checkCons gamma' (t+1) cs
>	          return (((cn,ccon):rest), gamma'')

checkScheme takes a raw iota scheme and returns a scheme with a well-typed
RHS (or fails if there is a type error).

For a scheme of the form

foo p0 p1 ... pn = t

we get V 0 = pn ... V n = p0
then pattern variables are retrieved by projection with Proj in typechecked t.

> checkScheme :: Gamma Name -> Name -> RawScheme -> IvorM (Scheme Name)
> checkScheme gamma n (RSch pats (RWRet ret)) = 
>     do let ps = map (mkPat gamma) pats
>	 let rhsvars = getPatVars gamma ps
>        let rhs = substVars gamma n rhsvars ret
>	 return (Sch (reverse ps) (Ind rhs))

Make a pattern from a raw term. Anything weird, just make it a "PTerm".

> mkPat :: Gamma Name -> Raw -> Pattern Name
> mkPat gam (Var n) = mkPatV n (lookupval n gam)
>        where mkPatV n (Just (DCon t x)) = PCon t n tyname []
>              mkPatV n (Just (TCon x _)) = PCon 0 n (UN "Type") []
>              mkPatV n _ = PVar n
>              tyname = case (getTyName gam n) of
>                         Just x -> x
> mkPat gam (RApp f a) = pat' (unwind f a)
>   where unwind (RApp f s) a = let (f',as) = unwind f s in
>				    (f',(mkPat gam a):as)
>	  unwind t a = (t, [mkPat gam a])
>         pat' (Var n, as) = mkPatV n (lookupval n gam) (reverse as)
>         pat' _ = PTerm

>         mkPatV n (Just (DCon t x)) as = PCon t n tyname as
>         mkPatV n (Just (TCon x _)) as = PCon 0 n (UN "Type") as
>         mkPatV _ _ _ = PTerm
>         tyname = case (getTyName gam (getname (getappfun f))) of
>                    Just x -> x
>         getname (Var n) = n
> mkPat gam _ {-(RBind _ _ _)-} = PTerm
> {-
> TODO: If a datatype has a placeholder in its indices, the value should
> be inferred (i.e. it should be checked) otherwise we can't make a pattern
> properly (and we'll certainly need this for optimisation)
> mkPat gam x = error $ "Can't make a pattern from " ++ show x
> -}

Get the pattern variables from the patterns, and work out what the projection 
function for each name is.

> getPatVars :: Gamma Name ->[Pattern Name] -> [(Name, TT Name)]
> getPatVars gam xs = pv' 0 (reverse xs)
>   where pv' i [] = []
>         pv' i (x:xs) = (project gam i x) ++ (pv' (i+1) xs)

	  indexify (n,t) = (n,Ind t)

Projection.

> project :: Gamma Name -> Int -> Pattern Name -> [(Name, TT Name)]
> project gam n x = project' n (\i -> V i) x
>   where project' n f (PVar x) = [(x,f n)]
>         project' n f (PCon _ fn ty es) = projargs n f 0 es ty
>         project' n f (PMarkCon fn es) = projargs n f 0 es (UN "FOO")
>         project' n f _ = [] -- Can't project from terms or marked vars.
>         projargs n f i [] _ = []
>         projargs n f i (PMark _:xs) ty = projargs n f i xs ty
>         projargs n f i (x:xs) ty
>             = (project' n ((\a -> (Proj ty i a)).f) x)
>               ++ projargs n f (i+1) xs ty

-- >         argtypes ty = case lookuptype ty gam of
-- >                          (Just (Ind ty)) -> map (getFnName.snd)
-- >                                               $ getExpected ty
-- >         getFnName (TyCon x _) = x
-- >         getFnName (App f x) = getFnName f
-- >         getFnName (Bind _ _ (Sc x)) = getFnName x
-- >         getFnName x = MN ("Dunno: "++show x, 0)

Make a RHS of an iota scheme, substituting names with projection operations.
ASSUMPTION: No bindings on the RHS. This should be true of all iota schemes.
Takes the name of the elimination rule and assumes any reference to an
elimination rule is a reference to this

> substVars :: Gamma Name -> Name -> [(Name,TT Name)] -> Raw -> TT Name
> substVars gam er ns r = sv' r
>    where sv' (Var x) = case (lookup x ns) of
>			    Nothing -> mkGood x
>			    (Just i) -> i
>	   sv' (RApp f a) = App (sv' f) (sv' a)
>          sv' (RConst c) = Const c

>          mkGood x = case (lookupval x gam) of
>	       (Just (DCon t i)) -> Con t x i
>              (Just (TCon i _)) -> TyCon x i
>              (Just (ElimRule _)) -> Elim er
>	       _ -> P x

> dummyRule :: ElimRule
> dummyRule _ = Nothing
