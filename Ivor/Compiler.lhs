> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Compiler(compile) where

> import Ivor.RunTT
> import Ivor.State
> import Ivor.Nobby
> import Ivor.Datatype
> import Ivor.TTCore
> import Ivor.ICompile

> import System.IO
> import Monad

> compile :: IState -> String -> IO ()
> compile st froot = 
>     do h <- openFile (froot++".hs") WriteMode
>        hPutStr h (header froot)
>        compileData (defs st) (datadefs st) st h
>        compileGamma (defs st) st h
>        hFlush h
>        hClose h

FIXME! Only does elim, not case.

> compileData :: Gamma Name -> [(Name,Datatype Name)] -> IState ->
>                Handle -> IO ()
> compileData gam [] st h = return ()
> compileData gam ((n,dt):xs) st h =
>     do let caseexp = compileSchemes (e_ischemes dt)
>        let arity = getArity (e_ischemes dt)
>        rn <- rulename    
>        if (length (datacons dt)>0) then
>           hPutStrLn h $ "data TT_" ++ exportName n ++ " = " ++ compileCons (datacons dt)
>           else hPutStrLn h $ "data TT_" ++ exportName n ++ " = TT_" ++ exportName n
>        let inst = projInstance (datacons dt)
>        when ((length (words inst))>0) 
>           $ hPutStrLn h $ "\ninstance Project TT_"++ exportName n ++
>                 " where\n" ++ inst
>        let rtt = mkRTElim n arity caseexp
>        let fn = mkGHC st rn arity rtt
>        hPutStrLn h fn
>        --putStrLn $ elimInterface n (snd (erule dt))
>        --putStrLn $ elimBody n rn (snd (erule dt))
>        --hPutStrLn h $ show rtt
>        compileData gam xs st h
>  where rulename = case lookupval n gam of
>                      (Just (TCon _ (Elims x _))) -> return x
>                      Nothing -> fail "No such type"

This creation of elim rule interfaces only works for completely simple types!

> elimInterface :: Name -> Indexed Name -> String
> elimInterface n (Ind ty) = "elim_" ++ exportName n ++ " :: " ++ mkET ty
>    where mkET (Bind _ (B Pi ty) (Sc sc)) = mkArg ty ++ mkET sc
>          mkET _ = "a"
>          mkArg ty | Star <- getReturnType ty = "" -- Skip Phi
>                   | TyCon x _ <- getFun ty 
>                        = "TT_" ++ exportName x ++ " -> "
>                   | otherwise = "(" ++ mkET ty ++ ") -> "

> elimBody :: Name -> Name -> Indexed Name -> String
> elimBody n rn (Ind ty) = "elim_" ++ exportName n ++ " = " ++ mkLams ty 0 ++
>                          "(coerce (fn_" ++ exportName rn ++ " " ++ mkET ty 0
>                          ++ "))::a"
>    where
>          mkET (Bind _ (B Pi ty) (Sc sc)) n | Star <- getReturnType ty
>                                                = mkArg ty n ++ mkET sc n
>          mkET (Bind _ (B Pi ty) (Sc sc)) n = mkArg ty n ++ mkET sc (n+1)
>          mkET _ _ = ""
>          mkLams (Bind _ (B Pi ty) (Sc sc)) n | Star <- getReturnType ty
>                                                = mkLams sc n        
>          mkLams (Bind _ (B Pi ty) (Sc sc)) n = "\\x"++show n ++ " -> "
>                                                ++ mkLams sc (n+1)
>          mkLams _ _ = ""

>          mkArg ty n | Star <- getReturnType ty = "((coerce Type)::val)"
>                     | otherwise = "((coerce x"++show n++")::val)"

> compileCons :: [(Name,Gval Name)] -> String
> compileCons [] = ""
> compileCons [x] = compileCon x
> compileCons (x:xs) = compileCon x ++ "| " ++ compileCons xs

> compileCon (n,G (DCon _ _) (Ind t)) =
>     foralls numargs ++ "TT_" ++ show n ++ " " ++ showargs numargs
>   where numargs = length (getExpected t)
>         foralls n | n == 0 = ""
>                   | otherwise = "forall arg. "
>         showargs 0 = ""
>         showargs n = "arg " ++ showargs (n-1)

> projInstance :: [(Name,Gval Name)] -> String
> projInstance [] = ""
> projInstance (x:xs) = 
>     let xp = projAll x in
>        if (length (words xp)>0) then xp ++ "\n" ++ projInstance xs
>           else projInstance xs

> projAll (n,G (DCon _ _) (Ind t)) =
>     project numargs
>   where numargs = length (getExpected t)
>         project 0 = "\n"
>         project k = "    project "++show (k-1)++" (TT_" ++ exportName n ++
>                     " " ++ showargs numargs++") = ((coerce a" ++ show (k-1)
>                         ++ ")::val)\n" ++ project (k-1)
>         showargs 0 = ""
>         showargs n = showargs (n-1) ++ " a" ++ show (n-1)

> compileGamma :: Gamma Name -> IState -> Handle -> IO ()
> compileGamma gam@(Gam g) st h = cg g where
>   cg [] = return ()
>   cg ((n,G (Fun _ ind) indty):xs) = 
>       do -- putStrLn $ "Compiling " ++ show n
>          let nind = normalise (Gam []) ind
>          let rtt = mkRTFun gam (levelise nind)
>          let (Ind ty) = normalise gam indty
>          let arity = length (getExpected ty)
>          let fn = mkGHC st n arity rtt
>          hPutStrLn h fn
>          cg xs
>   cg (x:xs) = do -- putStrLn $ "Skipping " ++ show x
>                  cg xs

> mkGHC :: IState -> Name -> Int -> RunTT -> String
> mkGHC st n arity tm = "fn_" ++ exportName n ++ " :: " ++ mkSig arity ++ "\n" ++
>                       "fn_" ++ exportName n ++ " = " ++ mkBody 0 tm ++ "\n"
>    where mkSig 0 = "val"
>          mkSig n = "val -> " ++ mkSig (n-1)
>          mkBody l (RTVar i) = "v"++show i
>          mkBody l (RTFun n) = "fn_" ++ exportName n
>          mkBody l (RTCon _ n args) = "(coerce (TT_" ++ exportName n ++ " " ++ showargs l args ++ ")::val)"
>          mkBody l (RTElim n t m ms) = "(fn_" ++ exportName n ++ " " ++ showarg l t ++
>                                     " ((coerce Type)::val) " ++ showargs l ms
>          mkBody l (RTApp f xs) = "(" ++ showfun l f (length xs) ++ " " ++ showargs l xs ++ ")"
>          mkBody l (RTBind (RTLam,_) (sc,_)) = "(\\v"++show l ++" -> " ++ mkBody (l+1) sc ++ ")"
>          mkBody l (RTBind (RTLet (v,_),_) (sc,_)) = "(let v"++show l ++" = " ++ "(" ++ mkBody l v ++ ") in (" ++ mkBody (l+1) sc ++ "))"
>          mkBody l (RTBind (RTPi,_) (sc,_)) = "((coerce Type)::val)"
>          mkBody l RTypeVal = "((coerce Type)::val)"
>          mkBody l RTCantHappen = "error \"Impossible\""
>          mkBody l (RTProj ty i (v,_)) = "(project " ++ show i ++ 
>                                      "((coerce " ++ mkBody l v ++")::TT_"++show ty++"))"
>          mkBody l (RTCase ty (v,_) xs) = "(case ((coerce "++mkBody l v++")::TT_"++show ty++") of { " ++ doCaseBody l (getCons (datadefs st) ty) xs ++ "})"
>          mkBody l (RTConst c) = error "Sorry, can't compile constants yet"
>          -- mkBody l x = "[[Not done "++show x++"]]"

>          doCaseBody l [] [] = ""
>          doCaseBody l ((n,ar):ns) (i:is) = doCase l n ar i ++ " ; " ++ doCaseBody l ns is 
>          doCase l n ar (i,_) = "TT_"++exportName n++" "++caseargs ar++" -> " ++ mkBody l i
>          caseargs 0 = ""
>          caseargs n = "_ "++caseargs (n-1)

>          showargs l [] = ""
>          showargs l (x:xs) = showarg l x ++ " " ++ showargs l xs
>          showarg l (x,_) = "((coerce "++mkBody l x++")::val)"
>          showfun l (f,_) n = "((coerce "++mkBody l f++")::"++mkty n++")"

>          mkty 0 = "val"
>          mkty n = "val->"++mkty (n-1)

Given a type name, get all the constructors and their arities

> getCons :: [(Name,Datatype Name)] -> Name -> [(Name,Int)]
> getCons ds n = case lookup n ds of
>                  Nothing -> []
>                  Just dt -> map (\ (x,y) -> (x, arity y)) (datacons dt)
>     where arity (G _ (Ind ty)) = length (getExpected ty)

> header mod = "{-# OPTIONS_GHC -fglasgow-exts #-} \n\
>               \\n\
>               \module " ++ mod ++ " where\n\
>               \\n\
>               \import GHC.Base\n\
>               \\n\
>               \coerce :: a -> b\n\
>               \coerce = unsafeCoerce#\n\
>               \\n\
>               \data Type = forall a. Type a\n\
>               \data Val = Val\n\
>               \\n\
>               \class Project x where\n\
>               \    project :: forall val. Int -> x -> val\n\n"

> exportName :: Name -> String
> exportName (UN n) = show $ UN (okch n)
>    where okch [] = []
>          okch ('\'':xs) = "_AP_"++okch xs
>          okch (x:xs) = x:(okch xs)
