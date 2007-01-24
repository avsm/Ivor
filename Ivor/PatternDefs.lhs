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
> generateAll gam fn ty _ = do
>   x <- expandCon gam (mkapp (Var (UN "S")) [mkapp (Var (UN "S")) [Var (UN "x")]])
>   --x <- expandCon gam (mkapp (Var (UN "vcons")) [RInfer,RInfer,RInfer,mkapp (Var (UN "vnil")) [Var (UN "foo")]])
>   fail $ show x

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
