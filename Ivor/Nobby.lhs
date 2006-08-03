> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Nobby where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant

> import Debug.Trace
> import List
> import Data.Typeable

To begin, we need to define the context in which normalisation takes place.
The context maps names to user defined functions, constructors and
elimination rules.

Global represents all possible global names --- if it's a user defined
name, hold its definition, otherwise hold what it is so we know what
to do with it, when the time comes.

> data Global n
>     = Fun [FunOptions] (Indexed n)    -- User defined function
>     | Partial (Indexed n) [n] -- Unfinished definition
>     | ElimRule ElimRule  -- Elimination Rule
>     | PrimOp PrimOp      -- Primitive function
>     | DCon Int Int       -- Data Constructor, tag and arity
>     | TCon Int (Elims n) -- Type Constructor and arity, elim rule name
>     | Unreducible        -- Unreducible name
>     | Undefined          -- Declared but undefined name

> data Elims n = Elims { elimRuleName :: n,
>                        caseRuleName :: n }

> data FunOptions = Frozen | Recursive
>   deriving Eq

> instance Show n => Show (Global n) where
>     show (Fun opts t) = "Fun " ++ show t
>     show (ElimRule _) = "<<elim rule>>"
>     show (PrimOp _) = "<<primitive operator>>"
>     show (DCon x t) = "DCon " ++ show x ++ "," ++show t
>     show (TCon x (Elims e c)) = "TCon " ++ show x
>     show Unreducible = "Unreducible"
>     show Undefined = "Undefined"

> data Gval n = G (Global n) (Indexed n)
>    deriving Show

> getglob (G v t) = v
> gettype (G v t) = t

> newtype Gamma n = Gam [(n,Gval n)]
>     deriving Show

> extend (Gam x) (n,v) = Gam ((n,v):x)

> emptyGam = Gam []

> lookupval :: Eq n => n -> Gamma n -> Maybe (Global n)
> lookupval n (Gam xs) = fmap getglob (lookup n xs)

> lookuptype :: Eq n => n -> Gamma n -> Maybe (Indexed n)
> lookuptype n (Gam xs) = fmap gettype (lookup n xs)

> glookup ::  Eq n => n -> Gamma n -> Maybe (Global n,Indexed n)
> glookup n (Gam xs) = fmap (\x -> (getglob x,gettype x)) (lookup n xs)

> insertGam :: n -> Gval n -> Gamma n -> Gamma n
> insertGam nm val (Gam gam) = Gam $ (nm,val):gam

> concatGam :: Gamma n -> Gamma n -> Gamma n
> concatGam (Gam x) (Gam y) = Gam (x++y)

> setFrozen :: Eq n => n -> Bool -> Gamma n -> Gamma n
> setFrozen n freeze (Gam xs) = Gam $ sf xs where
>    sf [] = []
>    sf ((p,G (Fun opts v) ty):xs) 
>        | n == p = (p,G (Fun (doFreeze freeze opts) v) ty):xs
>    sf (x:xs) = x:(sf xs)
>    doFreeze True opts = nub (Frozen:opts)
>    doFreeze False opts = opts \\ [Frozen]

> setRec :: Eq n => n -> Bool -> Gamma n -> Gamma n
> setRec n frec (Gam xs) = Gam $ sf xs where
>    sf [] = []
>    sf ((p,G (Fun opts v) ty):xs) 
>        | n == p = (p,G (Fun (doFrec frec opts) v) ty):xs
>    sf (x:xs) = x:(sf xs)
>    doFrec True opts = nub (Recursive:opts)
>    doFrec False opts = opts \\ [Recursive]


> freeze :: Eq n => n -> Gamma n -> Gamma n
> freeze n gam = setFrozen n True gam

> thaw :: Eq n => n -> Gamma n -> Gamma n
> thaw n gam = setFrozen n False gam

Remove a name from the middle of the context - should only be valid
if it's a partial definition or an axiom which is about to be replaced.

> remove :: Eq n => n -> Gamma n -> Gamma n
> remove n (Gam xs) = Gam $ rm n xs where
>    rm n [] = []
>    rm n (d@(p,_):xs) | n==p = xs
>                      | otherwise = d:(rm n xs)

Insert a name into the context. If the name is already there, this
is an error *unless* the old definition was 'Undefined', in which case
the name is replaced.

> gInsert :: (Monad m, Eq n, Show n) => n -> Gval n -> Gamma n -> m (Gamma n)
> gInsert nm val (Gam xs) = do xs' <- ins nm val xs []
>                              return $ Gam xs'
>   where ins n val [] acc = return $ (n,val):(reverse acc)
>         -- FIXME: Check ty against val
>         ins n val (d@(p,G Undefined ty):xs) acc
>             | n == p = return $ (n,val):(reverse acc) ++ xs
>         ins n val (d@(p,_):xs) acc 
>             | n == p = fail $ "Name " ++ show p ++ " is already defined"
>             | otherwise = ins n val xs (d:acc)

An ElimRule is a Haskell implementation of the iota reductions of
a family.

> type ElimRule = Spine Value -> Maybe Value

A PrimOp is an external operation

> type PrimOp = Spine Value -> Maybe Value

Model represents normal forms, including Ready (reducible) and Blocked
(non-reducible) forms.

> data Model s = MR (Ready s)
>              | MB (Blocked s) (Spine (Model s))

> data Ready s 
>     = RdBind Name (Binder (Model s)) (s (Model s))
>     | RCon Int Name (Spine (Model s))
>     | RTyCon Name (Spine (Model s))
>     | forall c. Constant c => RdConst c
>     | RdStar
>     | RdLabel (Model s) (MComp s)
>     | RdCall (MComp s) (Model s)
>     | RdReturn (Model s)
>     | RdCode (Model s)
>     | RdQuote (Model s) -- (TT Name)

> data Blocked s
>     = BCon Int Name Int
>     | BTyCon Name Int
>     | BElim ElimRule Name
>     | BPrimOp PrimOp Name
>     | BRec Name Value
>     | BP Name
>     | BV Int
>     | BEval (Model s)
>     | BEscape (Model s)

> data MComp s = MComp Name [Model s]

> newtype Weakening = Wk Int

Second weakening is cached to prevent function composition in the weaken
class.

> newtype Kripke x = Kr (Weakening -> x -> x, Weakening)

> type Value = Model Kripke
> type Normal = Model Scope

> newtype Ctxt = VG [Value]

The normalisation function itself.

We take a flag saying whether this is for conversion checking or not. This is
necessary because staged evaluation will not reduce things inside a quote
to normal form, but we need a normal form to compare.

> nf :: Gamma Name -> Ctxt 
>    -> Bool -- ^ For conversion
>    -> TT Name -> Value
> nf g c conv t = {-trace (show t) $-} eval 0 g c t where
>  eval stage gamma (VG g) (V n) | (length g) <= n = MB (BV n) Empty
>                          | otherwise = g!!n
>  eval stage gamma g (P n) = evalP (lookupval n gamma)
>    where evalP (Just Unreducible) = (MB (BP n) Empty)
>          evalP (Just Undefined) = (MB (BP n) Empty)
>          evalP (Just (Partial (Ind v) _)) = (MB (BP n) Empty)
>          evalP (Just (PrimOp f)) = (MB (BPrimOp f n) Empty)
>          evalP (Just (Fun opts (Ind v))) 
> --               | Frozen `elem` opts && not conv = MB (BP n) Empty
>                -- recursive functions only reduce if at least one
>                -- argument is constructor headed
>                -- | Recursive `elem` opts 
>                --     = MB (BRec n (eval stage gamma g v)) Empty
>                -- | otherwise 
>                    = eval stage gamma g v
>          evalP _ = (MB (BP n) Empty)
>              --error $ show n ++ 
>	         --      " is not a function. Something went wrong."
>                    -- above error is unsound; if names are rebound.
>  eval stage gamma g (Con tag n 0) = (MR (RCon tag n Empty))
>  eval stage gamma g (Con tag n i) = (MB (BCon tag n i) Empty)
>  eval stage gamma g (TyCon n 0) = (MR (RTyCon n Empty))
>  eval stage gamma g (TyCon n i) = (MB (BTyCon n i) Empty)
>  eval stage gamma g (Const x) = (MR (RdConst x))
>  eval stage gamma g Star = MR RdStar
>  eval stage gamma (VG g) (Bind n (B Lambda ty) (Sc sc)) =
>      (MR (RdBind n (B Lambda (eval stage gamma (VG g) ty))
>         (Kr (\w x -> eval stage gamma (VG (x:(weaken w g))) sc,Wk 0))))
>  eval stage gamma (VG g) (Bind n (B (Let val) ty) (Sc sc)) =
>      eval stage gamma (VG ((eval stage gamma (VG g) val):g)) sc
>  eval stage gamma (VG g) (Bind n (B Pi ty) (Sc sc)) =
>      (MR (RdBind n (B Pi (eval stage gamma (VG g) ty))
>         (Kr (\w x -> eval stage gamma (VG (x:(weaken w g))) sc,Wk 0))))
>  eval stage gamma (VG g) (Bind n (B Hole ty) (Sc sc)) =
>      (MR (RdBind n (B Hole (eval stage gamma (VG g) ty))
>         (Kr (\w x -> eval stage gamma (VG (x:(weaken w g))) sc,Wk 0))))
>  eval stage gamma (VG g) (Bind n (B (Guess v) ty) (Sc sc)) =
>      (MR (RdBind n (B (Guess (eval stage gamma (VG g) v)) (eval stage gamma (VG g) ty))
>         (Kr (\w x -> eval stage gamma (VG (x:(weaken w g))) sc,Wk 0))))
>  eval stage gamma g (Proj _ x t) = case (eval stage gamma g t) of
>			 MR (RCon _ _ sp) -> (listify sp)!!x
>			 _ -> error "Foo" -- MB (BProj x (eval stage gamma g t))
>  eval stage gamma g (App f a) = apply g (eval stage gamma g f) (eval stage gamma g a)
>  eval stage gamma g (Call c t) = docall g (evalcomp stage gamma g c) (eval stage gamma g t)
>  eval stage gamma g (Label t c) = MR (RdLabel (eval stage gamma g t) (evalcomp stage gamma g c))
>  eval stage gamma g (Return t) = MR (RdReturn (eval stage gamma g t))
>  eval stage gamma g (Elim n) = MB (BElim (getelim (lookupval n gamma)) n) Empty
>    where getelim Nothing = \sp -> Nothing
>          getelim (Just (ElimRule x)) = x
>          getelim y = error $ show n ++ 
>            " is not an elimination rule. Something went wrong." ++ show y
>  eval stage gamma g (Stage s) = evalStage stage gamma g s

>  evalcomp stage gamma g (Comp n ts) = MComp n (map (eval stage gamma g) ts)

>  evalStage stage gamma g (Code t) = MR (RdCode (eval stage gamma g t))
>  evalStage stage gamma g (Quote t) = if conv
>     then -- let cd = (forget ((quote (eval stage gamma g t)::Normal))) in
>          --             MR (RdQuote cd)
>          MR (RdQuote (eval (stage+1) gamma g t))
>     -- This is again a bit of a hack, just evaluating without any definitions
>     -- but it is a nice cheap way of seeing what we'd have to generate code
>     -- for at run-time.
>     else MR (RdQuote (eval (stage+1) (Gam []) g t))
>     -- else let cd = (forget ((quote (eval (Gam []) g t)::Normal))) in
>        --               MR (RdQuote cd)
>        -- MR (RdQuote (substV g t)) --(splice t)) -- broken
>  evalStage stage gamma g (Eval t) = case (eval (stage+1) gamma g t) of
>                            (MR (RdQuote t')) -> eval stage gamma g 
>                                                   (forget ((quote t')::Normal))
>                            x -> MB (BEval x) Empty
>  evalStage stage gamma g (Escape t) = case (eval (stage+1) gamma g t) of
>                            (MR (RdQuote t')) -> 
>                                if (stage>0)
>                                   then t'
>                                   else eval stage gamma g (forget ((quote t')::Normal))
>                            x -> MB (BEscape x) Empty -- needed for conversion check
>                            --_ -> error $ "Can't escape something non quoted " ++ show t

> docall :: Ctxt -> MComp Kripke -> Value -> Value
> docall g _ (MR (RdReturn v)) = v
> docall g c v = MR (RdCall c v)

> apply :: Ctxt -> Value -> Value -> Value
> apply = app where -- oops
>  app g (MR (RdBind _ (B Lambda ty) k)) v = krApply k v
>  app g (MB (BElim e n) sp) v =
>      case e (Snoc sp v) of
>         Nothing -> (MB (BElim e n) (Snoc sp v))
>         (Just v) -> v
>  app g (MB (BPrimOp e n) sp) v =
>      case e (Snoc sp v) of
>         Nothing -> (MB (BPrimOp e n) (Snoc sp v))
>         (Just v) -> v
>  app g (MB (BCon tag n i) sp) v
>      | size (Snoc sp v) == i = (MR (RCon tag n (Snoc sp v)))
>      | otherwise = (MB (BCon tag n i) (Snoc sp v))
>  app g (MB (BTyCon n i) sp) v
>      | size (Snoc sp v) == i = (MR (RTyCon n (Snoc sp v)))
>      | otherwise = (MB (BTyCon n i) (Snoc sp v))
>  app g (MB bl sp) v = MB bl (Snoc sp v)
>  app g v a = error $ "Can't apply a non function " ++ show (forget ((quote v)::Normal)) ++ " to argument " ++ show (forget ((quote a)::Normal))

  constructorsIn Empty = False
  constructorsIn (Snoc xs (MR (RCon _ _ _))) = True
  constructorsIn (Snoc xs _) = constructorsIn xs

> krApply :: Kripke Value -> Value -> Value
> krApply (Kr (f,w)) x = f w x

 applySpine :: Ctxt -> Value -> Spine Value -> Value -> Value
 applySpine g fn Empty v = apply g fn v
 applySpine g fn (Snoc sp x) v = apply g (applySpine g fn sp x) v

Splice the escapes inside a term

> splice :: TT Name -> TT Name
> splice = mapSubTerm (splice.st) where
>   st (Stage (Escape (Stage (Quote t)))) = (splice t)
>   st x = x

> class Weak x where
>     weaken :: Weakening -> x -> x
>     weaken (Wk 0) x = x
>     weaken (Wk n) x = weakenp n x
>     weakenp :: Int -> x -> x

> instance Weak Int where
>     weakenp i j = i + j

> instance Weak Weakening where
>     weakenp i (Wk j) = Wk (i + j)

> instance Weak (Model Kripke) where
>     weakenp i (MR r) = MR (weakenp i r)
>     weakenp i (MB b sp) = MB (weakenp i b) (fmap (weakenp i) sp)

> instance Weak (Ready Kripke) where
>     weakenp i (RdBind n bind sc) = RdBind n (weakenp i bind) (weakenp i sc)
>     weakenp i (RdConst x) = RdConst x
>     weakenp i RdStar = RdStar
>     weakenp i (RCon t n sp) = RCon t n (fmap (weakenp i) sp)
>     weakenp i (RTyCon n sp) = RTyCon n (fmap (weakenp i) sp)
>     weakenp i (RdLabel t c) = RdLabel (weakenp i t) (weakenp i c)
>     weakenp i (RdCall c t) = RdCall (weakenp i c) (weakenp i t)
>     weakenp i (RdReturn t) = RdReturn (weakenp i t)
>     weakenp i (RdCode t) = RdCode (weakenp i t)
>     weakenp i (RdQuote t) = RdQuote (weakenp i t)

> instance Weak (TT Name) where
>     weakenp i t = vapp (\ (ctx,v) -> V (weakenp i v)) t

> instance Weak (MComp Kripke) where
>     weakenp i (MComp n ts) = MComp n (fmap (weakenp i) ts)

> instance Weak n => Weak (Binder n) where
>     weakenp i (B (Let v) ty) = B (Let (weakenp i v)) (weakenp i ty)
>     weakenp i (B (Guess v) ty) = B (Guess (weakenp i v)) (weakenp i ty)
>     weakenp i (B b ty) = B b (weakenp i ty)

> instance Weak (Blocked Kripke) where
>     weakenp i (BCon t n j) = BCon t n j
>     weakenp i (BTyCon n j) = BTyCon n j
>     weakenp i (BElim e n) = BElim e n
>     weakenp i (BRec n v) = BRec n v
>     weakenp i (BPrimOp e n) = BPrimOp e n
>     weakenp i (BP n) = BP n
>     weakenp i (BV j) = BV (weakenp i j)
>     weakenp i (BEval t) = BEval (weakenp i t)
>     weakenp i (BEscape t) = BEscape (weakenp i t)

> instance Weak (Kripke x) where
>     weakenp i (Kr (f,w)) = Kr (f,weakenp i w)

> instance Weak Ctxt where
>     weakenp i (VG g) = VG (weakenp i g)

> instance Weak x => Weak [x] where
>     weakenp i xs = fmap (weakenp i) xs

> class Quote x y where
>     quote :: x -> y

> instance Quote Value Normal where
>     quote (MR r) = MR (quote r)
>     quote (MB b sp) = MB (quote b) (fmap quote sp)

> instance Quote (Ready Kripke) (Ready Scope) where
>     quote (RdConst x) = RdConst x
>     quote RdStar = RdStar
>     quote (RdBind n b sc) = RdBind n (quote b) (Sc (quote (krquote sc)))
>     quote (RCon t c sp) = RCon t c (fmap quote sp)
>     quote (RTyCon c sp) = RTyCon c (fmap quote sp)
>     quote (RdLabel t c) = RdLabel (quote t) (quote c)
>     quote (RdCall c t) = RdCall (quote c) (quote t)
>     quote (RdReturn t) = RdReturn (quote t)
>     quote (RdCode t) = RdCode (quote t)
>     quote (RdQuote t) = RdQuote (quote t)

> instance Quote (Blocked Kripke) (Blocked Scope) where
>     quote (BCon t n j) = BCon t n j
>     quote (BTyCon n j) = BTyCon n j
>     quote (BElim e n) = BElim e n
>     quote (BRec n v) = BRec n v
>     quote (BPrimOp e n) = BPrimOp e n
>     quote (BP n) = BP n
>     quote (BV j) = BV j
>     quote (BEval t) = BEval (quote t)
>     quote (BEscape t) = BEscape (quote t)

> instance Quote (MComp Kripke) (MComp Scope) where
>     quote (MComp n ts) = MComp n (fmap quote ts)

> krquote :: Kripke Value -> Value
> krquote (Kr (f,w)) = f (weaken w (Wk 1)) (MB (BV 0) Empty)

> instance Quote n m => Quote (Binder n) (Binder m) where
>     quote (B b ty) = B (quote b) (quote ty)

> instance Quote n m => Quote (Bind n) (Bind m) where
>     quote (Let v) = Let (quote v)
>     quote (Guess v) = Guess (quote v)
>     quote Lambda = Lambda
>     quote Pi = Pi
>     quote Hole = Hole

> instance Forget Normal (TT Name) where
>     forget (MB b sp) = makeApp (forget b) (fmap forget sp)
>     forget (MR r) = forget r

> instance Forget (Blocked Scope) (TT Name) where
>     forget (BCon t n j) = Con t n j
>     forget (BTyCon n j) = TyCon n j
>     forget (BElim e n) = Elim n
>     forget (BRec n v) = P n
>     forget (BPrimOp f n) = P n
>     forget (BP n) = P n
>     forget (BV i) = V i
>     forget (BEval t) = Stage (Eval (forget t))
>     forget (BEscape t) = Stage (Escape (forget t))

> instance Forget (Ready Scope) (TT Name) where
>     forget (RdBind n b (Sc sc)) = Bind n (forget b) (Sc (forget sc))
>     forget (RdConst x) = (Const x)
>     forget RdStar = Star
>     forget (RCon t c sp) = makeApp (Con t c (size sp)) (fmap forget sp)
>     forget (RTyCon c sp) = makeApp (TyCon c (size sp)) (fmap forget sp)
>     forget (RdLabel t c) = Label (forget t) (forget c)
>     forget (RdCall c t) = Call (forget c) (forget t)
>     forget (RdReturn t) = Return (forget t)
>     forget (RdCode t) = Stage (Code (forget t))
>     forget (RdQuote t) = Stage (Quote (forget t))

> instance Forget (MComp Scope) (Computation Name) where
>     forget (MComp n ts) = Comp n (fmap forget ts)

> instance Forget (Binder (Model Scope)) (Binder (TT Name)) where
>     forget (B b ty) = B (forget b) (forget ty)

> instance Forget (Bind (Model Scope)) (Bind (TT Name)) where
>     forget (Let v) = Let (forget v)
>     forget (Guess v) = Guess (forget v)
>     forget Lambda = Lambda
>     forget Pi = Pi
>     forget Hole = Hole

> makeApp :: TT Name -> Spine (TT Name) -> TT Name
> makeApp f Empty = f
> makeApp f (Snoc xs x) = (App (makeApp f xs)) x

> normalise :: Gamma Name -> (Indexed Name) -> (Indexed Name)
> normalise g (Ind t) = Ind (forget (quote (nf g (VG []) False t)::Normal))

> convNormalise :: Gamma Name -> (Indexed Name) -> (Indexed Name)
> convNormalise g (Ind t) = Ind (forget (quote (nf g (VG []) True t)::Normal))

> normaliseEnv :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> normaliseEnv env g t
>     = normalise (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g) 
>             = addenv xs (Gam ((n,G (Fun [] (Ind v)) (Ind ty)):g))
>         addenv (_:xs) g = addenv xs g

> convNormaliseEnv :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> convNormaliseEnv env g t
>     = convNormalise (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g) 
>             = addenv xs (Gam ((n,G (Fun [] (Ind v)) (Ind ty)):g))
>         addenv (_:xs) g = addenv xs g

     = Ind (forget (quote (nf g (VG (valenv env [])) t)::Normal))
    where valenv [] env = trace (show (map forget ((map quote env)::[Normal]))) $ env
          valenv ((n,B (Let v) ty):xs) env = valenv xs ((eval env v):env)
          valenv ((n,B _ ty):xs) env = valenv xs ((MB (BP n) Empty):env)
          eval env v = nf g (VG env) v

> natElim :: ElimRule
> natElim (Snoc args@(Snoc (Snoc (Snoc Empty phi) phiZ) phiS)  
>            (MR (RCon 0 (UN "O") sp)))
>      = return phiZ
> natElim (Snoc args@(Snoc (Snoc (Snoc Empty phi) phiZ) phiS)  
>            (MR (RCon 1 (UN "S") (Snoc Empty n))))
>      = return (apply (VG []) (apply (VG []) phiS n)
>                  (apply (VG []) rec n))
>    where rec = (MB (BElim natElim (UN "nateElim")) args)
> natElim _ = Nothing

> genElim :: Int -> Int -> [(Name,Ctxt -> Value)] -> ElimRule
> genElim arity con red sp
>   | size sp < arity = Nothing
>   | otherwise = case (sp??con) of
>        (MR (RCon t n args)) -> 
>              do v <- lookup n red
>                 let ctx = VG $ (makectx args)++(makectx (lose con sp))
>                 return $ v ctx
>        _ -> Nothing
>   where makectx (Snoc xs x) = x:(makectx xs)
>         makectx Empty = []


====================== Functors for contexts ===============================

> instance Functor Gamma where
>     fmap f (Gam xs) = Gam (fmap (\ (x,y) -> (f x,fmap f y)) xs)

> instance Functor Gval where
>     fmap f (G g i) = G (fmap f g) (fmap f i)

> instance Functor Global where
>     fmap f (Fun opts n) = Fun opts $ fmap f n
>     fmap f (ElimRule e) = ElimRule e
>     fmap f (DCon t i) = DCon t i
>     fmap f (TCon i (Elims en cn)) = TCon i (Elims (f en) (f cn))


> arity :: Gamma Name -> Indexed Name -> Int
> arity g t = ca (normalise g t)
>    where ca (Ind t) = ca' t
>          ca' (Bind _ (B Pi _) (Sc r)) = 1+(ca' r)
>          ca' _ = 0