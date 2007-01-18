> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.PatternDefs where

> import Ivor.Gadgets
> import Ivor.TTCore
> import Ivor.Datatype
> import Ivor.Nobby
> import Ivor.Typecheck

> import Debug.Trace

Use the iota schemes from Datatype to represent pattern matching definitions.

> type PMRaw = RawScheme
> type PMDef n = Scheme n

> data PMFun n = PMFun [PMDef n]
>    deriving Show

> checkDef :: Monad m => Gamma Name -> Name -> Raw -> [PMRaw] -> m (PMFun Name)
> checkDef gam n ty rschs = do 
>     schs <- mapM (checkClause gam n ty) rschs
>     -- TODO: Coverage and termination checking
>     return $ PMFun schs

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



 checkClause gam n (RSch pats ret) =
     
