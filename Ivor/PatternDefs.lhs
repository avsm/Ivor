> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.PatternDefs where

> import Ivor.Gadgets
> import Ivor.TTCore
> import Ivor.Datatype
> import Ivor.Nobby
> import Ivor.Typecheck

> import Debug.Trace
> import Data.List

Use the iota schemes from Datatype to represent pattern matching definitions.

> checkDef :: Monad m => Gamma Name -> Name -> Raw -> [PMRaw] -> 
>             m (PMFun Name, Indexed Name)
> checkDef gam fn tyin pats = do 
>   --x <- expandCon gam (mkapp (Var (UN "S")) [mkapp (Var (UN "S")) [Var (UN "x")]])
>   --x <- expandCon gam (mkapp (Var (UN "vcons")) [RInfer,RInfer,RInfer,mkapp (Var (UN "vnil")) [Var (UN "foo")]])
>   clausesIn <- mapM (expandClause gam) pats
>   let clauses = nub (concat clausesIn)
>   let clauses' = filter (mostSpecClause clauses) clauses
>   (ty@(Ind ty'),_) <- typecheck gam tyin
>   let arity = length (getExpected ty')
>   checkNotExists fn gam
>   gam' <- gInsert fn (G Undefined ty) gam
>   clauses' <- validClauses gam' fn ty clauses'
>   pmdef <- matchClauses gam' fn pats tyin clauses'
>   checkWellFounded pmdef
>   return (PMFun arity pmdef, ty)
>     where checkNotExists n gam = case lookupval n gam of
>                                 Just Undefined -> return ()
>                                 Just _ -> fail $ show n ++ " already defined"
>                                 Nothing -> return ()


A definition is well founded if, for every clause, there is an argument
position i such that all recursive calls have an argument in position i 
which is structurally smaller than the pattern in position i.

TODO!

> checkWellFounded :: Monad m => [PMDef Name] -> m ()
> checkWellFounded _ = return ()

For each Raw clause, try to match it against a generated and checked clause.
Match up the inferred arguments to the names (so getting the types of the
names bound in patterns) then type check the right hand side.

> matchClauses :: Monad m => Gamma Name -> Name -> [PMRaw] -> Raw -> 
>                 [(Indexed Name, Indexed Name)] -> m [PMDef Name]
> matchClauses gam fn pats tyin gen = do
>    let raws = zip (map mkRaw pats) (map getRet pats)
>    checkpats <- mapM (mytypecheck gam) raws
>    checkCoverage (map fst checkpats) (map fst gen)
>    return $ map (mkScheme gam) checkpats

    where mkRaw (RSch pats r) = mkPBind pats tyin r
          mkPBind [] _ r = r
          mkPBind (p:ps) (RBind n (B _ t) tsc) r 
              = RBind n (B (Pattern p) t) (mkPBind ps tsc r)

>   where mkRaw (RSch pats r) = mkapp (Var fn) pats
>         getRet (RSch pats r) = r
>         mytypecheck gam (clause, ret) = 
>             do (tm, pty, env) <- typecheckAndBind gam clause
>                (rtm, rty) <- check gam env ret Nothing 
>                checkConvEnv env gam pty rty $ "Pattern error: " ++ show pty ++ " and " ++ show rty ++ " are not convertible"
>                return (tm, rtm)

> mkScheme :: Gamma Name -> (Indexed Name, Indexed Name) -> PMDef Name
> mkScheme gam (Ind pat, ret) = Sch (map mkpat (getPatArgs pat)) ret
>   where mkpat (P n) = PVar n
>         mkpat (App f a) = addPatArg (mkpat f) (mkpat a)
>         mkpat (Con i nm ar) = mkPatV nm (lookupval nm gam)
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

> checkCoverage :: Monad m => [Indexed Name] -> [Indexed Name] -> m ()
> checkCoverage pats [] = return ()
> checkCoverage pats (c:cs)
>     | length (filter (matches c) pats) > 0 = checkCoverage pats cs
>     | otherwise = fail $ "Missing clause: " ++ show c

> matches (Ind p) (Ind t) = matches' p t
> matches' (App f a) (App f' a') = matches' f f' && matches' a a'
> matches' (Con _ x _) (Con _ y _) | x == y = True
> matches' (TyCon x _) (TyCon y _) | x == y = True
> matches' (P x) (P y) | x == y = True
> matches' (P (MN ("INFER",_))) _ = True
> matches' _ (P _) = True
> matches' x y = x == y


> expandClause :: Monad m => Gamma Name -> RawScheme -> m [RawScheme]
> expandClause gam (RSch ps ret) = do
>   expanded <- mapM (expandCon gam) ps
>   return $ map (\p -> RSch p ret) (combine expanded)

Remove the clauses which can't possibly be type correct.

> validClauses :: Monad m => Gamma Name -> Name -> Indexed Name -> 
>                 [RawScheme] -> m [(Indexed Name, Indexed Name)]
> validClauses gam fn ty cs = do
>     -- add fn:ty to the context as an axiom
>     checkValid gam [] cs
>  where checkValid gam acc [] = return acc
>        checkValid gam acc ((RSch c r):cs) 
>           = do let app = mkapp (Var fn) c
>                case typecheck gam app of
>                  Nothing -> checkValid gam acc cs
>                  Just (v,t) -> checkValid gam ((v,t):acc) cs


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


> showClauses [] = ""
> showClauses ((x,r):xs) = show x ++ " -> " ++ show r ++ "\n" ++ showClauses xs


Given a raw term, recursively expand all of its arguments which are in
constructor form

> expandCon :: Monad m => Gamma Name -> Raw -> m [Raw]
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