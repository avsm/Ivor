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

> type PMRaw = RawScheme
> type PMDef n = Scheme n

> data PMFun n = PMFun [PMDef n]
>    deriving Show

> checkDef :: Monad m => Gamma Name -> Name -> Raw -> [PMRaw] -> m (PMFun Name)
> checkDef gam n ty rschs = do 
>     cases <- generateAll gam n ty rschs
>     fail "unfinished"
>     -- schs <- mapM (checkClause gam n ty) rschs
>     -- TODO: Coverage and termination checking
>     -- return $ PMFun schs

> checkClause :: Monad m => Gamma Name -> Name -> Raw -> PMRaw -> 
>                m (PMDef Name)
> checkClause gam n ty sch@(RSch args ret) = trace (show sch) $ do
>     (argscheck, bs) <- checkArgs [] args ty
>     (ret, _) <- check gam bs (getrettype ty) Nothing
>     return $ Sch argscheck ret
>   where checkArgs bindings [] _ = return ([], bindings)
>         checkArgs bindings (x:xs) (RBind nm (B Pi t) ts) = trace (show x ++ " : " ++ show t ++ ", " ++ show bindings) $ do
>             (xcheck, bs) <- checkPatt gam bindings Nothing x t
>             (Ind tyc, _) <- check gam bs t (Just (Ind Star))
>             (xscheck, bs') <- checkArgs ((nm,B Pi tyc):bs) xs ts
>             return (xcheck:xscheck, bs')

         mkEnv = map (\ (n,Ind t) -> (n, B Pi t))

> generateAll :: Monad m => Gamma Name -> Name -> Raw -> [PMRaw] -> m [PMRaw]
> generateAll gam fn tyin pats = do
>   --x <- expandCon gam (mkapp (Var (UN "S")) [mkapp (Var (UN "S")) [Var (UN "x")]])
>   --x <- expandCon gam (mkapp (Var (UN "vcons")) [RInfer,RInfer,RInfer,mkapp (Var (UN "vnil")) [Var (UN "foo")]])
>   clausesIn <- mapM (expandClause gam) pats
>   let clauses = nub (concat clausesIn)
>   let clauses' = filter (mostSpecClause clauses) clauses
>   (ty,_) <- typecheck gam tyin
>   clauses' <- validClauses gam fn ty clauses'
>   fail $ showClauses clauses'

> expandClause :: Monad m => Gamma Name -> RawScheme -> m [[Raw]]
> expandClause gam (RSch ps ret) = do
>   expanded <- mapM (expandCon gam) ps
>   return $ combine expanded

Remove the clauses which can't possibly be type correct

> validClauses :: Monad m => Gamma Name -> Name -> Indexed Name -> 
>                 [[Raw]] -> m [[Raw]]
> validClauses gam fn ty cs = do
>     -- add fn:ty to the context as an axiom
>     checkNotExists fn gam
>     gam' <- gInsert fn (G Undefined ty) gam
>     checkValid gam' [] cs
>  where checkValid gam acc [] = return acc
>        checkValid gam acc (c:cs) 
>           = do let app = mkapp (Var fn) c
>                case typecheck gam app of
>                  Nothing -> checkValid gam acc cs
>                  Just _ -> checkValid gam (c:acc) cs
>        checkNotExists n gam = case lookupval n gam of
>                                 Just Undefined -> return ()
>                                 Just _ -> fail $ show n ++ " already defined"
>                                 Nothing -> return ()


Return true if the given pattern clause is the most specific in a list

> mostSpecClause :: [[Raw]] -> [Raw] -> Bool
> mostSpecClause cs c = msc c (filter (/= c) cs)
>    where msc c [] = True
>          msc c (x:xs) | moreSpecClause x c = False
>                       | otherwise = msc c xs

> moreSpecClause :: [Raw] -> [Raw] -> Bool
> moreSpecClause [] [] = True
> moreSpecClause (x:xs) (y:ys)
>       | moreSpec x y = moreSpecClause xs ys
>       | x == y = moreSpecClause xs ys
>       | otherwise = False


> showClauses [] = ""
> showClauses (x:xs) = showClause x ++ "\n" ++ showClauses xs

> showClause [] = " -> "
> showClause (r:rs) = "(" ++ show r ++ ") " ++ showClause rs

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
>     let (Var tyname) = getappfun (getrettype (forget conty))
>     TCon i (Elims _ _ cons) <- lookupval tyname gam
>     return $ map (\n -> (n, arity n)) cons
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
