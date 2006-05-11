> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.SC where

Lambda lifter. Two bits:

lift: Takes a TT function definition and returns a set of supercombinators.
elimSC: Takes a simple case expression and returns a supercombinator.

> import Ivor.Grouper
> import Ivor.TTCore
> import Ivor.Nobby
> import Ivor.ICompile
> import Ivor.Constant

> import Debug.Trace

> data SCName = N Name
>             | SN Name Int
>   deriving Eq

> instance Show SCName where
>     show (N n) = show n
>     show (SN n i) = "$"++show n ++show i

> type SCs = [(SCName, (Int, SC))]

> data SC = SLam [SCBody] SCBody

> data SCBody
>     = SP SCName
>     | SV Int
>     | SCon Int SCName [SCBody]
>     | STyCon SCName Int
> {-     | SElim SCName -}
>     | SApp SCBody [SCBody]
>     | SLet SCBody SCBody SCBody
>     | SPi SCBody SCBody
>     | SProj Int SCBody
>     | forall c. Constant c => SConst c
>     | SStar
>     | SCase Int [SCBody]
>     | SCantHappen
>     | SSomeType
>  -- deriving Show

Turn a well typed term with de Bruijn levels into a set of supercombinators.
The main supercombinator will have the given name

> lift :: Name -> Levelled Name -> SCs
> lift basename t = collect basename (group (fmap N t))

> collect :: Name -> GroupTT SCName -> [(SCName,(Int,SC))]
> collect basename g = snd $ sc (N basename) [] 0 [] g where
>    sc name args next scs (GLam args' lev body)
>        = let (next',scs',scargs) = sclist args next scs args'
>              (next'',scs'',scb) = scbody (args++scargs) next' scs' body 
>              newsc = SLam (args++scargs) scb in
>              (next'',((name, (length (args++scargs),newsc)):scs''))
>    sc name args next scs body
>        = let (next',scs',scb) = scbody [] next scs body
>              newsc = SLam [] scb in
>	       (next',((name,(0,newsc)):scs'))

Do the tricky case first.  
This is the quick hack version; it ought to
check that previously bound variables are actually used.

>    scbody args next scs b@(GLam args' l body) 
>        = let (next',scs') = sc (SN basename next) args (next+1) scs
>		                 (GLam args' 0 body) in
>          (next',scs',mkapp (SP (SN basename next)) (argvals args))
>      where mkapp x [] = x
>            mkapp x as = SApp x as
>            argvals xs = map SV [0..(length xs)-1]

Everything else is pretty much structural...

>    scbody args next scs (GP n) = (next, scs, SP n)
>    scbody args next scs (GV i) = (next, scs, SV i)
>    scbody args next scs (GCon i n as) =
>             let (next',scs',scas) = sclist args next scs as in
>	      (next',scs',SCon i n scas)
>    scbody args next scs (GTyCon n i) = (next,scs,STyCon n i)
>    scbody args next scs (GElim n) = (next, scs, SP n)
>    scbody args next scs (GApp f as) =
>             let (next',scs',scf) = scbody args next scs f 
>                 (next'',scs'',scas) = sclist args next' scs' as in
>	      (next'',scs'',SApp scf scas)
>    scbody args next scs (GLet t v sc) =
>             let (next',scs',sct) = scbody args next scs t
>                 (next'',scs'',scv) = scbody args next' scs' v
>                 (next''',scs''',scsc) = scbody (args++[sct]) next'' scs'' sc in
>	      (next''',scs''',SLet sct scv scsc)
>    scbody args next scs (GPi t sc) =
>             let (next',scs',sct) = scbody args next scs t
>                 (next'',scs'',scsc) = scbody args next' scs' sc in
>	      (next'',scs'',SPi sct scsc)
>    scbody args next scs (GProj i t) =
>             let (next',scs',sct) = scbody args next scs t in
>	      (next',scs',SProj i sct)
>    scbody args next scs (GConst c) = (next,scs,SConst c)
>    scbody args next scs GStar = (next,scs,SStar)
>    scbody _ next scs GCant = (next,scs,SCantHappen)

>    sclist args next scs [] = (next,scs,[])
>    sclist args next scs (x:xs) 
>          = let (next',scs',xsc) = scbody args next scs x
>                (next'',scs'',xscs) = sclist args next' scs' xs in
>                (next'',scs'',xsc:xscs)


Turn a simple case tree into a supercombinator

> elimSC :: Name -> Levelled Name -> SimpleCase -> SC
> elimSC ename (Lev rtype) es = SLam (mkargs rtype) (mksc es)
>    where mksc Impossible = SCantHappen
>          mksc (IReduce t) = mkreduce (mkvarnum t)
>          mksc (Case _ x cs) = SCase (arity-x-1)
>		                  (map mksc cs)
>          mkvarnum (Ind t) = vapp (\ (ctx,i) -> V (arity-i-1)) t
>          args = mkargs rtype
>          arity = length args

    Reductions will have no lambdas, so an easy, boring, structural job.
   
>          mkreduce (P n) = SP (N n)
>          mkreduce (Elim n) = SP (N n)
>          mkreduce (V x) = SV x
>	   mkreduce ap@(App f a) = mkapp ap []
>          mkreduce (Proj _ i t) = SProj i (mkreduce t)
>          mkreduce (TyCon n i) = STyCon (N n) i
>          mkreduce (Con i t a) = SSomeType
>          mkreduce x = SSomeType

>          mkapp (App f a) sp = mkapp f ((mkreduce a):sp)
>          mkapp x sp = SApp (mkreduce x) sp

>          mkargs (Bind n (B Pi t) (Sc sc)) = (mkreduce t):(mkargs sc)
>          mkargs t = []

Ugly printer

> instance Show SC where
>     show = showSC


> showSCs :: SCs -> String
> showSCs [] = ""
> showSCs ((n,(a,sc)):xs) = show n ++ "("++show a++") = " ++ showSC sc ++ "\n" ++ showSCs xs

> showSC (SLam args body) = "\\" ++ showargs 0 args ++ " -> " ++ showBody body
>   where showargs i [] = ""
>         showargs i (x:xs) = "v" ++ show i ++ ":" ++ showBody x ++ " " ++ showargs (i+1) xs

> showBody (SP n) = show n
> showBody (SV i) = "v"++show i
> showBody (SCon i n bs) = show n ++ "<" ++ showBs bs ++ ">"
> showBody (STyCon n i) = show n
> --showBody (SElim n) = show n
> showBody (SApp f as) = showBody f ++ "(" ++ showBs as ++ ")"
> showBody (SLet t v b) = "let " ++ showBody v ++ ":" ++ showBody t ++ " in "
>					   ++ showBody b
> showBody (SPi t sc) = "{"++showBody t++"}"++showBody sc
> showBody (SProj i sc) = "("++showBody sc++")!"++show i
> showBody (SConst c) = show c
> showBody (SCantHappen) = "Impossible"
> showBody (SSomeType) = "Unknown"
> showBody (SCase e cs) = "case v" ++ show e ++ " {" ++ showBs cs ++ "}"
> showBody (SStar) = "*"

> showBs [] = ""
> showBs [x] = showBody x
> showBs (x:xs) = showBody x ++ "," ++ showBs xs
