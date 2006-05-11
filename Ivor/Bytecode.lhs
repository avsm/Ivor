> module Ivor.Bytecode where

Compilation of supercombinators to bytecode

> import Ivor.SC
> import Ivor.TTCore

> type Arity = Int
> type Tag = Int
> type TmpVar = Int

> type Bytecode = [ByteOp]

> data ByteOp
>     = STARTFN SCName Arity -- Needed?
>     | DECLARE Int
>     | TMP Int
>     | RETURN TmpVar
>     | CALL TmpVar SCName [TmpVar]
>     | CON TmpVar Tag [TmpVar]
>     | CLOSURE TmpVar SCName [TmpVar]
>     | VAR TmpVar Int
>     | GETARG TmpVar Int TmpVar
>     | CLOSUREADD TmpVar TmpVar [TmpVar]
>     | EVAL Int
>     | EVALTMP TmpVar
>     | TYPE TmpVar
>     | TAILCALL SCName [TmpVar]
>     | ALET Int TmpVar
>     | CASE Int [Bytecode]
>  deriving Show

> data FunInfo
>     = FI {
>         bytecode :: Bytecode,
>         cname :: String,
>         ctag :: String,
>         farity :: Int,
>         ctagid :: Int
>       }
>   deriving Show

> type ByteDef = [(SCName,FunInfo)]

I wonder how generally useful this is...

> mapInc :: (Int->a->b) -> [a] -> Int -> [b]
> mapInc f [] i = []
> mapInc f (x:xs) i = (f i x):(mapInc f xs (i+1))

> compileAll :: SCs -> SCs -> ByteDef
> compileAll ctxt group = mapInc scomp group ((length ctxt)-(length group))
>    where scomp i (n,(a,sc)) = (n,FI (adddecls a (scompile n ctxt sc))
>		                      (mkcname n)
>		                      (mkctag n)
>			              a
>			              i)
>          mkcname (N n) = "_EVM_"++show n
>          mkcname (SN n i) = "_EVMSC_"++show i++"_"++show n
>          mkctag  (N n) = "FTAG_EVM_"++show n
>          mkctag  (SN n i) = "FTAG_EVMSC_"++show i++"_"++show n

> scompile :: SCName -> SCs -> SC -> Bytecode
> scompile name scs (SLam args body) =
>    (STARTFN name (length args)):(bcomp (length args) 0 body)
>   where
>      getarity n = case lookup n scs of
>		       (Just (a,d)) -> a
>	               Nothing -> error $ "Can't happen (scompile, name "++show n++", " ++ show (map fst scs)++ ")"
>      bcomp v t (SCase scr alts) = 
>         (EVAL scr):
>         [CASE scr (map (acomp v t) alts)]
>      bcomp v t (SApp (SP n) as) 
>             | getarity n == length as = 
>	          concat (mapInc (ecomp v) as (t+1))
>		     ++ [TAILCALL n (mktargs (length as) (t+1))]
>      bcomp v t x = (ecomp v t x)++[RETURN t]

>      mktargs 0 s = []
>      mktargs n s = s:(mktargs (n-1) (s+1))

>      acomp v t x = bcomp v t x -- Hmm. Well, maybe alts will get more complex

>      ecomp :: Int -> TmpVar -> SCBody -> Bytecode
>      ecomp v t (SP n) | getarity n == 0 = [CALL t n []]
>		        | otherwise = [CLOSURE t n []]
>   --   ecomp v (SElim n) | getarity n == 0 = CALL n []
>   --		         | otherwise = CLOSURE n []
>      ecomp v t (SV i) = [VAR t i]
>      ecomp v t (SCon tag n as) 
>	          = concat (mapInc (ecomp v) as (t+1))
>		     ++ [CON t tag (mktargs (length as) (t+1))]

>      ecomp v t (SApp f as) = fcomp v t f as
>      ecomp v t (SLet val ty b) = 
>                (ecomp v (t+1) val) ++
>	         (ALET v (t+1)):
>	         (ecomp (v+1) (t+2) b)
>      ecomp v t (SProj i b) = (ecomp v (t+1) b) ++
>		       [GETARG  t i (t+1)]
>      ecomp v t (SPi e ty) = [TYPE t]
>      ecomp v t SStar = [TYPE t]
>      ecomp v t (SConst c) = error "Can't compile constants yet"
>      ecomp v t _ = [TYPE t]

>      fcomp v t (SP n) as 
>          | getarity n == length as
>               = concat (mapInc (ecomp v) as (t+1))
>                   ++ [CALL t n (mktargs (length as) (t+1))]
>          | otherwise 
>               = concat (mapInc (ecomp v) as (t+1))
>                   ++ [CLOSURE t n (mktargs (length as) (t+1))]

>      fcomp v t f as 
>	          = (ecomp v (t+1) f) ++
>	             concat (mapInc (ecomp v) as (t+2))
>		     ++ [CLOSUREADD t (t+1) (mktargs (length as) (t+2))]

>      -- ccomp Star t = [TYPE t]

Add type declarations to the top of bytecode, for the benefit of C/C--.

> adddecls :: Int -> Bytecode -> Bytecode
> adddecls arity bc = let (tmps,vars) = fd (-1,-1) bc in
>                         ad (tmps+1) (vars+1) ++ bc
>   where ad 0 n | n<=arity = []
>         ad 0 (n+1) = (DECLARE n):(ad 0 n)
>         ad (m+1) n = (TMP m):(ad m n)

>         fd (t,v) [] = (t,v)
>         fd (t,v) (c:cs) = let (t',v') = fd' (t,v) c in
>				fd (t',v') cs

>         fd' (t,v) (RETURN rt) | rt>t = (rt,v)
>			        | otherwise = (t,v)
>         fd' (t,v) (CALL tv _ _)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (CON tv _ _)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (CLOSURE tv _ _)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (CLOSUREADD tv _ _)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (VAR tv _)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (GETARG tv _ _)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (TYPE tv)
>               | tv > t = (tv,v)
>		| otherwise = (t,v)	    
>         fd' (t,v) (ALET vv _)
>               | vv > v = (t,vv)
>	        | otherwise = (t,v)
>	  fd' (t,v) (CASE _ bs) = fdcs (t,v) bs
>         fd' ts _ = ts

>         fdcs (t,v) [] = (t,v)
>	  fdcs (t,v) (c:cs) = let (t',v') = fd (t,v) c in
>				  fdcs (t',v') cs

