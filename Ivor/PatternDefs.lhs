> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.PatternDefs where

> import Ivor.Gadgets
> import Ivor.TTCore
> import Ivor.Nobby
> import Ivor.Typecheck
> import Ivor.Unify
> import Ivor.Errors

> import Debug.Trace
> import Data.List
> import Control.Monad

Use the iota schemes from Datatype to represent pattern matching definitions.

Return the definition, and auxiliary definitions,
and their types, as well as any other names which need
to be defined to complete the definition.
Also return whether the function is definitely total.

> checkDef :: Gamma Name -> Name -> Raw -> [PMRaw] -> 
>             Bool -> -- Check for coverage
>             Bool -> -- Check for well-foundedness
>             IvorM ([(Name, PMFun Name, Indexed Name)], [(Name, Indexed Name)], Bool)
> checkDef gam fn tyin pats cover wellfounded = do
>   --x <- expandCon gam (mkapp (Var (UN "S")) [mkapp (Var (UN "S")) [Var (UN "x")]])
>   --x <- expandCon gam (mkapp (Var (UN "vcons")) [RInfer,RInfer,RInfer,mkapp (Var (UN "vnil")) [Var (UN "foo")]])
>   clausesIn <- mapM (expandClause gam) pats
>   let clauses = nub (concat clausesIn)
>   let clauses' = filter (mostSpecClause clauses) clauses
>   (ty@(Ind ty'),_) <- typecheck gam tyin
>   let arity = length (getExpected ty')
>   checkNotExists fn gam
>   gam' <- gInsert fn (G Undefined ty defplicit) gam
>   clauses' <- validClauses gam' fn ty clauses'
>   (pmdefs, newdefs, covers) <- matchClauses gam' fn pats tyin ty cover clauses'
>   wf <- return True 
>         {- if wellfounded then
>             do checkWellFounded gam fn [0..arity-1] pmdef
>                return True
>            else case checkWellFounded gam fn [0..arity-1] pmdef of
>                   Nothing -> return False
>                   _ -> return True -}
>   let total = wf && covers
>   return (pmdefs, newdefs, total)
>     where checkNotExists n gam = case lookupval n gam of
>                                 Just Undefined -> return ()
>                                 Just _ -> fail $ show n ++ " already defined"
>                                 Nothing -> return ()


1) A definition is well founded if, for every clause, there is an argument
position i such that all recursive calls have an argument in position i
which is structurally smaller than the pattern in position i.

An argument position is considered 'well-founded' if
in any recursive call, it has a structurally smaller argument.

A clause is well-founded if there are no recursive calls, or it has a
well-founded argument in common with all other recursive calls. We keep a list
of which arguments are well-founded

[REMOVED: Nested recursive calls are not allowed]
[They are allowed as long as they are also well-founded]

2) Alternatively, a definition is well founded if in every recursive call
there are no increasing arguments and at least one decreasing argument.

> checkWellFounded :: Gamma Name ->
>                     Name -> -- recursive function name
>                     [Int] -> -- set of well founded args
>                     [PMDef Name] -> IvorM ()
> checkWellFounded gam fn args cs = case cwf1 fn args cs of
>                                     Failure err -> cwf2 fn cs err
>                                     Success v -> return ()
>   where cwf1 fn args [] = return ()
>         cwf1 fn args (c:cs) = do args <- wfClause args c
>                                  cwf1 fn args cs
>
>         cwf2 fn [] _ = return ()
>         cwf2 fn (c:cs) err = do allDec c err
>                                 cwf2 fn cs err

Check for definition 1 above: one argument position is well founded

>         wfClause args (Sch pats (Ind t)) = do
>            let recs = findRec [] t
>            case recs of
>               [] -> return args
>               _ ->  wfRec args pats recs Nothing

Check for definition 2 above: all recursive calls have a decreasing argument
and no increasing arguments

>         allDec (Sch pats (Ind t)) err = do
>            let recs = findRec [] t
>            case allRecDec pats recs of
>              Success v -> return v
>              _ -> fail err

Check each recursive call has at least one decreasing argument and no
increasing arguments (iterature through calls)

>         allRecDec _ [] = return ()
>         allRecDec pats (r:rs) = do oneDec pats r 0 False
>                                    allRecDec pats rs

Check each recursive call has at least one decreasing argument and no
increasing arguments (iterature through arguments in a call)

>         oneDec [] [] i True = return ()
>         oneDec [] [] i False = fail "No decreasing arguments"
>         oneDec (p:ps) (c:cs) i smaller
>                | structurallySmaller c p = oneDec ps cs (i+1) True
>                | ss True c p = oneDec ps cs (i+1) smaller
>                | otherwise = fail $ show c ++ " bigger than " ++ show p

>         findRec args (App f a) = findRec (a:args) f
>         findRec args (P n) | n == fn = [args] ++
>                                        -- find nested calls too
>                                        (concat $ map (findRec []) args)
>         findRec args (Label t _) = findRec [] t
>                                    ++ (concat (map (findRec []) args))
>         findRec args (Bind _ (B (Let v) _) (Sc sc)) = findRec [] v ++
>                                                     findRec [] sc
>                                    ++ (concat (map (findRec []) args))
>         findRec args (Bind _ _ (Sc sc)) = findRec [] sc
>                                    ++ (concat (map (findRec []) args))
>         findRec args _ = concat $ map (findRec []) args

>         wfRec [] _ _ (Just last) = fail $ "Not a well-founded call: "
>                                             ++ show last
>         wfRec args pats [] _ = return args
>         wfRec args pats (a:as) _ =
>             {- case concat (map (findRec []) a) of
>                (_:_) -> fail $ "Nested recursive calls not allowed "
>                                ++ show (mkRec a)
>                _ -> -}
>               do args <- wfRec1 args 0 pats a
>                  wfRec args pats as (Just (mkRec a))

>         mkRec as = appArgs (P fn) as

>         wfRec1 args i [] [] = return args
>         wfRec1 args i (p:ps) (a:as)
>             | structurallySmaller a p = wfRec1 args (i+1) ps as
>             | otherwise = wfRec1 (args \\ [i]) (i+1) ps as
>         wfRec1 args i _ _ = return args -- variadic function, just stop looking

A non-recursive constructor application is structurally smaller than
anything.

>         structurallySmaller n p = ss False n p
>         ss True n p | pattEq n p = True -- inside, check for equality
>         ss _ n (PCon _ _ _ ps) = any (ss True n) ps -- look under cons
>         ss _ n p | isNonrec (getFun n) = True
>         ss _ _ _ = False

>         pattEq (P n) (PVar n') = n == n'
>         pattEq (Con t _ _) (PCon t' _ _ []) = t == t'
>         pattEq (App f a) (PCon t' _ _ xs) = eqApp t' (App f a) (reverse xs)
>             where eqApp t (App f a) (x:xs) = pattEq a x && eqApp t f xs
>                   eqApp t (Con t' _ _) [] = t == t'
>                   eqApp _ _ _ = False
>         pattEq _ _ = False

>         isNonrec (Con _ n _) = not (recCon n gam)
>         isNonrec _ = False

For each Raw clause, try to match it against a generated and checked clause.
Match up the inferred arguments to the names (so getting the types of the
names bound in patterns) then type check the right hand side.

Each clause may generate auxiliary definitions, so return all definitons created.

> matchClauses :: Gamma Name -> Name -> [PMRaw] -> Raw -> Indexed Name -> 
>                 Bool -> -- Check coverage
>                 [(Indexed Name, Indexed Name)] -> 
>                 IvorM ([(Name, PMFun Name, Indexed Name)], [(Name, Indexed Name)], Bool)
> matchClauses gam fn pats tyin ty@(Ind ty') cover gen = do
>    let raws = zip (map mkRaw pats) (map getRet pats)
>    (checkpats, newdefs, aux, covers) <- mytypechecks gam raws [] [] [] True
>    cv <- if cover then 
>              do checkCoverage (map fst checkpats) (map fst gen)
>                 return True
>              else case checkCoverage (map fst checkpats) (map fst gen) of
>                 Left err -> return False
>                 _ -> return True
>    let pmdef = map (mkScheme gam) checkpats
>    let arity = length (getExpected ty')
>    return $ ((fn, PMFun arity pmdef, ty) : aux , newdefs, cv && covers)

    where mkRaw (RSch pats r) = mkPBind pats tyin r
          mkPBind [] _ r = r
          mkPBind (p:ps) (RBind n (B _ t) tsc) r
              = RBind n (B (Pattern p) t) (mkPBind ps tsc r)

>   where mkRaw (RSch pats r) = mkapp (Var fn) pats
>         getRet (RSch pats r) = r
>         mytypechecks gam [] acc defs auxdefs cov = return (reverse acc, auxdefs, defs, cov)
>         mytypechecks gam (c:cs) acc defs auxdefs cov =
>             do ((cl, cr, _), newdefs, aux', covd) <- mytypecheck gam c (length cs)
>                mytypechecks gam cs ((cl,cr):acc) (defs++newdefs) (auxdefs++aux') (cov && covd)
>         mytypecheck gam (clause, (RWRet ret)) i = 
>             do (tm@(Ind tmtt), pty,
>                 rtm@(Ind rtmtt), rty, env, newdefs) <- checkAndBindPair gam clause ret
>                unified <- unifyenv gam env pty rty
>                let gam' = foldl (\g (n,t) -> extend g (n,G Undefined t 0))
>                                   gam newdefs
>                let rtmtt' = substNames unified rtmtt
>                -- checkConvEnv env gam pty rty $ "Pattern error: " ++ show pty ++ " and " ++ show rty ++ " are not convertible " ++ show unify
>                let namesret = filter (notGlobal gam') $ getNames (Sc rtmtt')
>                let namesbound = getNames (Sc tmtt)
>                checkAllBound (fileLine ret) namesret namesbound (Ind rtmtt') tmtt rty pty
>                -- trace (show (unified, rtmtt, tm, rtmtt')) $ 
>                return ((tm, Ind rtmtt', newdefs), [], newdefs, True)
>         mytypecheck gam (clause, (RWith scr pats)) i =
>             do -- Get the type of scrutinee, construct the type of the auxiliary definition
>                (tm@(Ind clausett), clausety, _, scrty@(Ind stt), env) <- checkAndBindWith gam clause scr fn
>                let args = getRawArgs clause
>                -- let restTyin = addLastArg tyin (forget scrty) scr
>                margs <- getMatches tm tm
>                let margNames = nub (map fst margs)
>                let newargs = filter (\ (x,ty) -> x `elem` margNames) env
>                newpats <- mapM (getNewPat tm 1) pats
>                let newfntyin = forget (mkNewTy newargs clausety)
>                let newfntyin' = addLastArg newfntyin (forget stt) scr
>                   --(newargs ++ [(UN "__scr", B Pi stt),
>                   --                                (UN "__scrEq", B Pi (screq (UN "__scr") scr))]) clausety
>                (newfnTy, _) <- trace (show newfntyin') $ check gam env newfntyin' (Just (Ind Star))
>                -- Make a name for the new function, clauses in 'pats' need the new name,
>                -- and form a definition of type restTy
>                let newname = mkNewName fn i
>                -- TODO: All pats have to match against args ++ [_]
>                -- Final clause returns newname applied to args++scrutinee++refl
>                let ret = rawApp (Var newname) ((map Var (map fst newargs)) ++ 
>                                                [scr, RApp (RApp (Var (UN "refl")) RInfer) RInfer])
>                let gam' = insertGam newname (G Undefined newfnTy 0) gam
>                newpdef <- mapM (newp tm newargs 1) (zip newpats pats)
>                (chk, auxdefs, _, _) <- trace (show (newfnTy, newpdef)) $ mytypecheck gam' (clause, (RWRet ret)) i
>                (auxdefs', newdefs, covers) <- checkDef gam' newname (forget newfnTy) newpdef False cover
>                return (chk, auxdefs++auxdefs', newdefs, covers)

>         addLastArg (RBind n (B Pi arg) x) ty scr = RBind n (B Pi arg) (addLastArg x ty scr)
>         addLastArg x ty scr = RBind (UN "__scr") (B Pi ty) 
>                                  (RBind (UN "__scrEq") (B Pi (screq (UN "__scr") scr)) x)

>         screq scrname scr = RApp (RApp (RApp (RApp (Var (UN "Eq")) RInfer) RInfer)
>                                (Var scrname)) scr

>         rawApp f [] = f
>         rawApp f (a:as) = rawApp (RApp f a) as

>         mkNewName (UN n) i = UN ("W__"++ n ++ "__" ++ show i) -- MN (n, i)
>         mkNewName (MN (n,j)) i = MN (n, (j + i + 255))

>         mkNewTy [] (Ind t) = t
>         mkNewTy ((x,b):ts) t = Bind x b (Sc (mkNewTy ts t))

>         getNewPat proto i (RSch args ret) = do
>             let pargs = rawApp (Var fn) (take (length args - i) args)
>             (argv, argt, _) <- checkAndBind gam [] pargs Nothing
>             getMatches argv proto

>         newp proto newargs i (newps, RSch args ret) = do
>             ret' <- newpRet ret
>             return $ RSch ((getAuxPats (map fst newargs) newps)++(lastn i args)++[RInfer]) ret'
>                 where newpRet (RWith v schs) = 
>                          do newpats <- mapM (getNewPat proto (i+1)) schs
>                             newpdef <- mapM (newp proto newargs (i+1)) (zip newpats schs)
>                             return (RWith v newpdef)
>                       newpRet r = return r

>         lastn i xs = reverse $ take i (reverse xs)

>         getAuxPats [] n = []
>         getAuxPats (x:xs) n = case lookup x n of
>                                 (Just t) -> (forget t):(getAuxPats xs n)

>         notGlobal gam n = case lookupval n gam of
>                               Nothing -> True
>                               _ -> False
>         checkAllBound fl r b rhs clause rhsTy clauseTy = do
>              let unbound = filter (\y -> not (elem y b)) r
>              if (length unbound == 0)
>                 then return ()
>                 else ifail $ addContext fl (IUnbound (Ind clause) clauseTy rhs rhsTy unbound)
>         addContext Nothing err = err
>         addContext (Just (f,l)) err = IContext (f ++ ":" ++ show l ++ ":") err

> mkScheme :: Gamma Name -> (Indexed Name, Indexed Name) -> PMDef Name
> mkScheme gam (Ind pat, ret) = Sch (map mkpat (getPatArgs pat)) ret
>   where mkpat (P n) = PVar n
>         mkpat (App f a) = addPatArg (mkpat f) (mkpat a)
>         mkpat (Con i nm ar) = mkPatV nm (lookupval nm gam)
>         mkpat (Const c) = PConst c
>         mkpat _ = PTerm

>         mkPatV n (Just (DCon t x)) = PCon t n (tyname n) []
>         mkPatV n _ = PVar n
>         tyname n = case (getTyName gam n) of
>                         Just x -> x

>         addPatArg (PCon i t ty args) arg = PCon i t ty (args++[arg])
>         addPatArg _ _ = PTerm

>         getPatArgs (App (P f) a) = [a]
>         getPatArgs (App f a) = getPatArgs f ++ [a]
>         getPatArgs _ = []

Return whether the patterns in the first argument cover the necessary
cases in the second argument. Each of the necessary cases in 'covering'
must match one of 'pats'.
fails, reporting which case isn't matched, if patterns don't cover.

> checkCoverage :: [Indexed Name] -> [Indexed Name] -> IvorM ()
> checkCoverage pats [] = return ()
> checkCoverage pats (c:cs)
>     | length (filter (matches c) pats) > 0 = checkCoverage pats cs
>     | otherwise = fail $ "Missing clause: " ++ show c

> matches p t = getMatches p t /= Nothing

> getMatches (Ind p) (Ind t) = matches' p t
> matches' (App f a) (App f' a') = do fm <- matches' f f'
>                                     am <- matches' a a'
>                                     return $ (fm ++ am)
> matches' (Con _ x _) (Con _ y _) | x == y = return []
> matches' (TyCon x _) (TyCon y _) | x == y = return []
> matches' (P x) (P y) | x == y = return [(y, P x)]
> matches' t (P n) = return [(n,t)]
> matches' (P nm@(MN ("INFER",_))) t = return []
> matches' x y = if x == y then return [] else fail "With pattern does not match parent"


> expandClause :: Gamma Name -> RawScheme -> IvorM [RawScheme]
> expandClause gam (RSch ps ret) = do
>   expanded <- mapM (expandCon gam) ps
>   return $ map (\p -> RSch p ret) (combine expanded)

Remove the clauses which can't possibly be type correct.

> validClauses :: Gamma Name -> Name -> Indexed Name ->
>                 [RawScheme] -> IvorM [(Indexed Name, Indexed Name)]
> validClauses gam fn ty cs = do
>     -- add fn:ty to the context as an axiom
>     checkValid gam [] cs
>  where checkValid gam acc [] = return acc
>        checkValid gam acc ((RSch c r):cs)
>           = do let app = mkapp (Var fn) c
>                case typecheck gam app of
>                  Right (v,t) -> checkValid gam ((v,t):acc) cs
>                  _ -> checkValid gam acc cs


Return true if the given pattern clause is the most specific in a list

> mostSpecClause :: [RawScheme] -> RawScheme -> Bool
> mostSpecClause cs c = msc c (filter (/= c) cs)
>    where msc c [] = True
>          msc c (x:xs) | moreSpecClause x c = False
>                       | otherwise = msc c xs

> moreSpecClause (RSch pa _) (RSch pb _)
>    = moreSpecClause' pa pb

> moreSpecClause' :: [Raw] -> [Raw] -> Bool
> moreSpecClause' [] [] = True
> moreSpecClause' (x:xs) (y:ys)
>       | moreSpec x y = moreSpecClause' xs ys
>       | x == y = moreSpecClause' xs ys
>       | otherwise = False
> -- Differing numbers of arguments; ignore it, it'll be caught as a type
> -- error elsewhere
> moreSpecClause' _ _ = False


> showClauses [] = ""
> showClauses ((x,r):xs) = show x ++ " -> " ++ show r ++ "\n" ++ showClauses xs


Given a raw term, recursively expand all of its arguments which are in
constructor form

> expandCon :: Gamma Name -> Raw -> IvorM [Raw]
> expandCon gam r = do
>     let f = getappfun r
>     let as = getappargs r
>     expandas <- mapM (expandCon gam) as
>     -- expandas contains all the possibilites for each argument
>     -- [[arg1poss1,arg1poss2,...], [arg2poss1,arg2pss2,...], ...]
>     case isConPatt gam f of
>         Nothing -> return.mostSpec $ expandf RInfer expandas
>         Just ns -> return.mostSpec $ (expandf f expandas) ++ (mkConPatts ns)
>   where expandf :: Raw -> [[Raw]] -> [Raw]
>         expandf f args = map (mkapp f) (combine args)
>         mkConPatts [] = []
>         mkConPatts ((n,ar):xs)
>            = (mkapp (Var n) (take ar (repeat RInfer))):(mkConPatts xs)

Turn a list of possibilities for each argument into a list of all
possible applications

> combine :: [[a]] -> [[a]]
> combine [] = [[]]
> combine [arg] = map (\x -> [x]) arg
> combine (arg:rest) = addEach arg (combine rest)
>     where addEach [] rest = []
>           addEach (x:xs) rest = (map (x:) rest) ++ (addEach xs rest)

Filter out more general entries; e.g. if (c _ _) and (c_ (d _)) keep the latter
only

> mostSpec :: [Raw] -> [Raw]
> mostSpec xs = ms' xs []
>   where ms' [] acc = acc
>         ms' (x:xs) acc | x `lessSpec` xs || x `lessSpec` acc = ms' xs acc
>                        | otherwise = ms' xs (x:acc)
>         lessSpec x [] = False
>         lessSpec x (y:ys) = (moreSpec y x) || x==y || (lessSpec x ys)

> moreSpec :: Raw -> Raw -> Bool
> moreSpec (Var _) (Var _) = False
> moreSpec RInfer RInfer = False
> moreSpec _ RInfer = True
> moreSpec (RApp x y) (RApp x2 y2) = moreSpec x x2 || (x==x2 && moreSpec y y2)
> moreSpec _ _ = False

Given a raw term, return whether it is a constructor pattern. If so,
return all of the constructor names and arities

> isConPatt :: Gamma Name -> Raw -> Maybe [(Name, Int)]
> isConPatt gam r | (Var name) <- getappfun r = do
>     conty <- lookuptype name gam
>     case getappfun (getrettype (forget conty)) of
>          (Var tyname) -> do
>              TCon i (Elims _ _ cons) <- lookupval tyname gam
>              return $ map (\n -> (n, arity n)) cons
>          _ -> Nothing
>                 | otherwise = Nothing
>   where arity nm = case lookuptype nm gam of
>                      Just (Ind ty) -> length (getExpected ty)
>                      -- Nothing can't happen

 checkClause gam n (RSch pats ret) =

 generateAll :: Monad m => Gamma Name -> Name -> Raw -> [PMRaw] -> m [PMRaw]
 generateAll gam n tyin pats = do
   (Ind ty, tyty) <- typecheck gam tyin
   checkConv gam tyty (Ind Star) "Type of function must be of type *"
   let args = getPatPos (length (getArgs ty)) pats
   trace (show args) $ fail "unfinished"

Get the argument positions which have patterns in them (rather than match
anything or just variables)

 getPatPos :: Int -> [PMRaw] -> [Int]
 getPatPos numargs [] = [0..numargs-1]
 getPatPos numargs ((RSch pats ret):xs) =
     union (gpp 0 pats) (getPatPos numargs xs)
   where gpp pos [] = []
         gpp pos ((PCon _ _ _ _):xs) = pos:(gpp (pos+1) xs)
