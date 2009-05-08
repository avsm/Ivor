> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Nobby where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant

> import Data.List
> import Control.Monad
> import Data.Typeable
> import qualified Data.Map as Map

> import Debug.Trace

To begin, we need to define the context in which normalisation takes place.
The context maps names to user defined functions, constructors and
elimination rules.

Global represents all possible global names --- if it's a user defined
name, hold its definition, otherwise hold what it is so we know what
to do with it, when the time comes.

> data Global n
>     = Fun [FunOptions] (Indexed n)    -- User defined function
>     | Partial (Indexed n) [n] -- Unfinished definition
>     | PatternDef (PMFun n) Bool -- Pattern matching definition, totality
>     | ElimRule ElimRule  -- Elimination Rule
>     | PrimOp PrimOp EvPrim     -- Primitive function
>     | DCon Int Int       -- Data Constructor, tag and arity
>     | TCon Int (Elims n) -- Type Constructor and arity, elim rule name
>     | Unreducible        -- Unreducible name
>     | Undefined          -- Declared but undefined name

> data Elims n = Elims { elimRuleName :: n,
>                        caseRuleName :: n,
>                        constructors :: [n] }
>              | NoConstructorsYet

> data FunOptions = Frozen | Recursive | Total
>   deriving Eq

> instance Show n => Show (Global n) where
>     show (Fun opts t) = "Fun " ++ show t
>     show (ElimRule _) = "<<elim rule>>"
>     show (PrimOp _ _) = "<<primitive operator>>"
>     show (DCon x t) = "DCon " ++ show x ++ "," ++show t
>     show (TCon x (Elims e c cons)) = "TCon " ++ show x
>     show Unreducible = "Unreducible"
>     show Undefined = "Undefined"

> type Plicity = Int

> defplicit = 0

> data Ord n => Gval n = G (Global n) (Indexed n) Plicity
>    deriving Show

> getglob (G v t p) = v
> gettype (G v t p) = t
> getplicity (G v t p) = p

> newtype Ord n => Gamma n = Gam (Map.Map n (Gval n))
>     deriving Show

> extend (Gam x) (n,v) = Gam (Map.insert n v x)

> emptyGam :: Ord n => Gamma n
> emptyGam = Gam Map.empty

> getAList :: Ord n => Gamma n -> [(n,(Gval n))]
> getAList (Gam n) = Map.toAscList n

> lookupval :: (Ord n, Eq n) => n -> Gamma n -> Maybe (Global n)
> lookupval n (Gam xs) = fmap getglob (Map.lookup n xs)

> lookuptype :: (Ord n, Eq n) => n -> Gamma n -> Maybe (Indexed n)
> lookuptype n (Gam xs) = fmap gettype (Map.lookup n xs)

> glookup ::  (Ord n, Eq n) => n -> Gamma n -> Maybe (Global n,Indexed n)
> glookup n (Gam xs) = fmap (\x -> (getglob x,gettype x)) (Map.lookup n xs)

Get a type name from the context

> getTyName :: Monad m => Gamma Name -> Name -> m Name
> getTyName  gam n = case lookuptype n gam of
>                            Just (Ind ty) -> return $ getFnName ty
>                            Nothing -> fail $ "No such name " ++ show n
>   where getFnName (TyCon x _) = x
>         getFnName (App f x) = getFnName f
>         getFnName (Bind _ _ (Sc x)) = getFnName x
>         getFnName x = MN ("Dunno: "++show x, 0)

Return whether a name is a recursive constructor (i.e, its family name
occurs anywhere in its arguments).

> recCon :: Name -> Gamma Name -> Bool
> recCon n gam = case glookup n gam of
>                  (Just (DCon _ t, Ind ty)) ->
>                      checkRec (conFamily ty) (map snd (getExpected ty))
>                  _ -> False
>    where conFamily t = fname (getFun (getReturnType t))
>          fname (TyCon n _) = n
>          fname _ = MN ("ERROR!",0)
>          checkRec n [] = False
>          checkRec n (x:xs) = nameOccurs n (forget x) || checkRec n xs

> insertGam :: Ord n => n -> Gval n -> Gamma n -> Gamma n
> insertGam nm val (Gam gam) = Gam $ Map.insert nm val gam

> concatGam :: Ord n => Gamma n -> Gamma n -> Gamma n
> concatGam (Gam x) (Gam y) = Gam (Map.union x y)

> setFrozen :: (Ord n, Eq n) => n -> Bool -> Gamma n -> Gamma n
> setFrozen n freeze (Gam xs) = Gam $ Map.mapWithKey sf xs where
>    sf p (G (Fun opts v) ty plicit)
>        | n == p = (G (Fun (doFreeze freeze opts) v) ty plicit)
>    sf _ x = x
>    doFreeze True opts = nub (Frozen:opts)
>    doFreeze False opts = opts \\ [Frozen]

> setRec :: (Ord n, Eq n) => n -> Bool -> Gamma n -> Gamma n
> setRec n frec (Gam xs) = Gam $ Map.mapWithKey sf xs where
>    sf p (G (Fun opts v) ty plicit)
>        | n == p = (G (Fun (doFrec frec opts) v) ty plicit)
>    sf _ x = x
>    doFrec True opts = nub (Recursive:opts)
>    doFrec False opts = opts \\ [Recursive]


> freeze :: (Ord n, Eq n) => n -> Gamma n -> Gamma n
> freeze n gam = setFrozen n True gam

> thaw :: (Ord n, Eq n) => n -> Gamma n -> Gamma n
> thaw n gam = setFrozen n False gam

Remove a name from the middle of the context - should only be valid
if it's a partial definition or an axiom which is about to be replaced.

> remove :: (Ord n, Eq n) => n -> Gamma n -> Gamma n
> remove n (Gam xs) = Gam $ Map.delete n xs

Insert a name into the context. If the name is already there, this
is an error *unless* the old definition was 'Undefined', in which case
the name is replaced.

> gInsert :: (Monad m, Ord n, Eq n, Show n) => 
>            n -> Gval n -> Gamma n -> m (Gamma n)
> gInsert nm val (Gam xs) = case Map.lookup nm xs of
>         -- FIXME: Check ty against val
>       Nothing -> return $ Gam (Map.insert nm val xs)
>       Just (G Undefined ty _) -> return $ Gam (Map.insert nm val xs)
>       Just (G (TCon _ NoConstructorsYet) ty _) -> 
>                                  return $ Gam (Map.insert nm val xs)
>       Just _ -> fail $ "Name " ++ show nm ++ " is already defined"

An ElimRule is a Haskell implementation of the iota reductions of
a family.

> type ElimRule = Spine Value -> Maybe Value

A PrimOp is an external operation

> type PrimOp = Spine Value -> Maybe Value
> type EvPrim = [TT Name] -> Maybe (TT Name) -- same, but with tt terms rather than values

Model represents normal forms, including Ready (reducible) and Blocked
(non-reducible) forms.

> data Model s = MR (Ready s)
>              | MB (Blocked s, Model s) (Spine (Model s))

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
>     | RdInfer

> data Blocked s
>     = BCon Int Name Int
>     | BTyCon Name Int
>     | BElim ElimRule Name
>     | BPatDef (PMFun Name) Name
>     | BPrimOp PrimOp Name
>     | BRec Name Value
>     | BP Name
>     | BV Int
>     | BEval (Model s) (Model s)
>     | BEscape (Model s) (Model s)

> data MComp s = MComp Name [Model s]

> newtype Weakening = Wk Int

Second weakening is cached to prevent function composition in the weaken
class.

> newtype Kripke x = Kr (Weakening -> x -> x, Weakening)

> type Value = Model Kripke
> type Normal = Model Scope

> newtype Ctxt = VG [Value]

> type PatVals = [(Name, Value)]

The normalisation function itself.

We take a flag saying whether this is for conversion checking or not. This is
necessary because staged evaluation will not reduce things inside a quote
to normal form, but we need a normal form to compare.

> nf :: Gamma Name -> Ctxt
>    -> PatVals
>    -> Bool -- ^ For conversion
>    -> TT Name -> Value
> nf g c patvals conv t = eval 0 g c t where

Get the type of a given name in the context

>  pty n = case lookuptype n g of
>             (Just (Ind ty)) -> nf g c [] conv ty
>             Nothing -> error "Can't happen, no such name, Nobby.lhs"

Do the actual evaluation

>  eval stage gamma (VG g) (V n)
>      | (length g) <= n = MB (BV n, MR RdInfer) Empty -- error $ "Reference out of context! " ++ show n ++ ", " ++ show (length g) --
>      | otherwise = g!!n
>  eval stage gamma g (P n)
>      = case lookup n patvals of
>           Just val -> val
>           Nothing -> evalP (lookupval n gamma)
>    where evalP (Just Unreducible) = (MB (BP n,pty n) Empty)
>          evalP (Just Undefined) = (MB (BP n, pty n) Empty)
>          evalP (Just (PatternDef p@(PMFun 0 pats) _)) =
>              case patmatch gamma g pats [] of
>                 Nothing ->  (MB (BPatDef p n, pty n) Empty)
>                 Just v -> v
>          evalP (Just (PatternDef p _)) = (MB (BPatDef p n, pty n) Empty)
>          evalP (Just (Partial (Ind v) _)) = (MB (BP n, pty n) Empty)
>          evalP (Just (PrimOp f _)) = (MB (BPrimOp f n, pty n) Empty)
>          evalP (Just (Fun opts (Ind v)))
> --               | Frozen `elem` opts && not conv = MB (BP n) Empty
>                -- recursive functions don't reduce in conversion check, to
>                -- maintain decidability of typechecking
>                  | Recursive `elem` opts  && conv
>                    = MB (BP n, pty n) Empty
>                  | otherwise
>                    = eval stage gamma g v
>          evalP _ = (MB (BP n, pty n) Empty)
>              --error $ show n ++
>	         --      " is not a function. Something went wrong."
>                    -- above error is unsound; if names are rebound.
>  eval stage gamma g (Con tag n 0) = (MR (RCon tag n Empty))
>  eval stage gamma g (Con tag n i) = (MB (BCon tag n i, pty n) Empty)
>  eval stage gamma g (TyCon n 0) = (MR (RTyCon n Empty))
>  eval stage gamma g (TyCon n i) = (MB (BTyCon n i, pty n) Empty)
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
>			 MR (RCon _ _ sp) -> traceIndex (listify sp) x "Nobby.lhs, Proj"
>			 _ -> error "Foo" -- MB (BProj x (eval stage gamma g t))
>  eval stage gamma g (App f a) = apply gamma g (eval stage gamma g f) (eval stage gamma g a)
>  eval stage gamma g (Call c t) = docall g (evalcomp stage gamma g c) (eval stage gamma g t)
>  eval stage gamma g (Label t c) = MR (RdLabel (eval stage gamma g t) (evalcomp stage gamma g c))
>  eval stage gamma g (Return t) = MR (RdReturn (eval stage gamma g t))
>  eval stage gamma g (Elim n) = MB (BElim (getelim (lookupval n gamma)) n, pty n) Empty
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
>     else MR (RdQuote (eval (stage+1) (Gam Map.empty) g t))
>     -- else let cd = (forget ((quote (eval (Gam []) g t)::Normal))) in
>        --               MR (RdQuote cd)
>        -- MR (RdQuote (substV g t)) --(splice t)) -- broken
>  evalStage stage gamma g (Eval t ty) = case (eval (stage+1) gamma g t) of
>                            (MR (RdQuote t')) -> eval stage gamma g
>                                                   (forget ((quote t')::Normal))
>                            x -> MB (BEval x bty, bty) Empty
>     where bty = eval stage gamma g ty
>  evalStage stage gamma g (Escape t ty) = case (eval (stage+1) gamma g t) of
>                            (MR (RdQuote t')) ->
>                                if (stage>0)
>                                   then t'
>                                   else eval stage gamma g (forget ((quote t')::Normal))
>                            x -> MB (BEscape x bty, bty) Empty -- needed for conversion check
>     where bty = eval stage gamma g ty

>                            --_ -> error $ "Can't escape something non quoted " ++ show t

> docall :: Ctxt -> MComp Kripke -> Value -> Value
> docall g _ (MR (RdReturn v)) = v
> docall g c v = MR (RdCall c v)

> apply :: Gamma Name -> Ctxt -> Value -> Value -> Value
> apply gam = app where
>  app g (MR (RdBind _ (B Lambda ty) k)) v = krApply k v
>  app g (MB (BElim e n, ty) sp) v = error "Elimination rules are eliminated"
>  {-    case e (Snoc sp v) of
>         Nothing -> (MB (BElim e n, ty) (Snoc sp v))
>         (Just v) -> v -}
>  app g (MB pat@(BPatDef (PMFun ar pats) n, ty) sp) v
>      | size (Snoc sp v) == ar =
>         case patmatch gam g pats (listify (Snoc sp v)) of
>           Nothing -> (MB pat (Snoc sp v))
>           Just v -> v
>      | otherwise = MB pat (Snoc sp v)
>  app g (MB (BPrimOp e n, ty) sp) v
>    = case e (Snoc sp v) of
>        Nothing -> (MB (BPrimOp e n, ty) (Snoc sp v))
>        (Just v) -> v
>  app g (MB (BCon tag n i, ty) sp) v
>      | size (Snoc sp v) == i = (MR (RCon tag n (Snoc sp v)))
>      | otherwise = (MB (BCon tag n i, ty) (Snoc sp v))
>  app g (MB (BTyCon n i, ty) sp) v
>      | size (Snoc sp v) == i = (MR (RTyCon n (Snoc sp v)))
>      | otherwise = (MB (BTyCon n i, ty) (Snoc sp v))
>  app g (MB bl sp) v = MB bl (Snoc sp v)
>  app g v a = error $ "Can't apply a non function " ++ show (forget ((quote v)::Normal)) ++ " to argument " ++ show (forget ((quote a)::Normal))

  constructorsIn Empty = False
  constructorsIn (Snoc xs (MR (RCon _ _ _))) = True
  constructorsIn (Snoc xs _) = constructorsIn xs

> krApply :: Kripke Value -> Value -> Value
> krApply (Kr (f,w)) x = f w x

> patmatch :: Gamma Name -> Ctxt -> [PMDef Name] -> [Value] -> Maybe Value
> patmatch gam g [] _ = Nothing
> patmatch gam g ((Sch pats ret):ps) vs = case pm gam g pats vs ret [] of
>                         Nothing -> patmatch gam g ps vs
>                         Just v -> Just v

> pm :: Gamma Name -> Ctxt -> [Pattern Name] -> [Value] -> Indexed Name ->
>       [(Name, Value)] -> -- matches so far
>       Maybe Value
> pm gam g [] [] (Ind ret) vals = Just $ nf gam g vals False ret
> pm gam g (pat:ps) (val:vs) ret vals
>    = do newvals <- pmatch pat val vals
>         newvals <- checkdups newvals
>         pm gam g ps vs ret newvals
> pm _ _ _ _ _ _ = Nothing

> checkdups v = Just v

> pmatch :: Pattern Name -> Value -> [(Name,Value)] -> Maybe [(Name, Value)]
> pmatch PTerm x vs = Just vs
> pmatch (PVar n) v vs = Just ((n,v):vs)
> pmatch (PConst t) (MR (RdConst t')) vs = do tc <- cast t
>                                             if tc == t' then Just vs
>                                                    else Nothing
> pmatch (PCon t _ _ args) (MR (RCon t' _ sp)) vs | t == t' =
>    pmatches args (listify sp) vs
>   where pmatches [] [] vs = return vs
>         pmatches (a:as) (b:bs) vs = do vs' <- pmatch a b vs
>                                        pmatches as bs vs'
>         pmatches _ _ _ = Nothing
> pmatch _ _ _ = Nothing


 RCon Int Name (Spine (Model s))

 applySpine :: Ctxt -> Value -> Spine Value -> Value -> Value
 applySpine g fn Empty v = apply g fn v
 applySpine g fn (Snoc sp x) v = apply g (applySpine g fn sp x) v

Splice the escapes inside a term

> splice :: TT Name -> TT Name
> splice = mapSubTerm (splice.st) where
>   st (Stage (Escape (Stage (Quote t)) _)) = (splice t)
>   st x = x

> class Weak x where
>     weaken :: Weakening -> x -> x
>     weaken (Wk 0) x = x
>     weaken (Wk n) x = weakenp n x
>     weakenp :: Int -> x -> x

> instance Weak Int where
>     weakenp i j = i + j

> instance (Weak a, Weak b) => Weak (a,b) where
>     weakenp i (x,y) = (weakenp i x, weakenp i y)

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
>     weakenp i (BPatDef p n) = BPatDef p n
>     weakenp i (BRec n v) = BRec n v
>     weakenp i (BPrimOp e n) = BPrimOp e n
>     weakenp i (BP n) = BP n
>     weakenp i (BV j) = BV (weakenp i j)
>     weakenp i (BEval t ty) = BEval (weakenp i t) (weakenp i ty)
>     weakenp i (BEscape t ty) = BEscape (weakenp i t) (weakenp i ty)

> instance Weak (Kripke x) where
>     weakenp i (Kr (f,w)) = Kr (f,weakenp i w)

> instance Weak Ctxt where
>     weakenp i (VG g) = VG (weakenp i g)

> instance Weak x => Weak [x] where
>     weakenp i xs = fmap (weakenp i) xs

> class Quote x y where
>     quote :: x -> y
>     quote' :: [Name] -> x -> y
>     quote = quote' []

> instance Quote Value Normal where
>     quote' ns (MR r) = MR (quote' ns r)
>     quote' ns (MB (b, ty) sp) = MB (quote' ns b, quote' ns ty)
>                                    (fmap (quote' ns) sp)

> instance Quote (Ready Kripke) (Ready Scope) where
>     quote' ns (RdConst x) = RdConst x
>     quote' ns RdStar = RdStar
>     quote' ns (RdBind n b@(B _ ty) sc)
>             = let n' = mkUnique n ns in
>                        RdBind n' (quote' ns b)
>                                   (Sc (quote' (n':ns) (krquote ty sc)))
>        where mkUnique n ns | n `elem` ns =
>                                case n of
>                                   (UN nm) -> (mkUnique (MN (nm, 0)) ns)
>                                   (MN (nm,i)) -> (mkUnique (MN (nm, i+1)) ns)
>                            | otherwise = n

>     quote' ns (RCon t c sp) = RCon t c (fmap (quote' ns) sp)
>     quote' ns (RTyCon c sp) = RTyCon c (fmap (quote' ns) sp)
>     quote' ns (RdLabel t c) = RdLabel (quote' ns t) (quote' ns c)
>     quote' ns (RdCall c t) = RdCall (quote' ns c) (quote' ns t)
>     quote' ns (RdReturn t) = RdReturn (quote' ns t)
>     quote' ns (RdCode t) = RdCode (quote' ns t)
>     quote' ns (RdQuote t) = RdQuote (quote' ns t)

> instance Quote (Blocked Kripke) (Blocked Scope) where
>     quote' ns (BCon t n j) = BCon t n j
>     quote' ns (BTyCon n j) = BTyCon n j
>     quote' ns (BElim e n) = BElim e n
>     quote' ns (BPatDef p n) = BPatDef p n
>     quote' ns (BRec n v) = BRec n v
>     quote' ns (BPrimOp e n) = BPrimOp e n
>     quote' ns (BP n) = BP n
>     quote' ns (BV j) = BV j
>     quote' ns (BEval t ty) = BEval (quote' ns t) (quote' ns ty)
>     quote' ns (BEscape t ty) = BEscape (quote' ns t) (quote' ns ty)

> instance Quote (MComp Kripke) (MComp Scope) where
>     quote' ns (MComp n ts) = MComp n (fmap (quote' ns) ts)

> krquote :: Value -> Kripke Value -> Value
> krquote t (Kr (f,w)) = f (weaken w (Wk 1)) (MB (BV 0, t) Empty)

> instance Quote n m => Quote (Binder n) (Binder m) where
>     quote' ns (B b ty) = B (quote' ns b) (quote' ns ty)

> instance Quote n m => Quote (Bind n) (Bind m) where
>     quote' ns (Let v) = Let (quote' ns v)
>     quote' ns (Guess v) = Guess (quote' ns v)
>     quote' ns Lambda = Lambda
>     quote' ns Pi = Pi
>     quote' ns Hole = Hole

Quotation to eta long normal form. DOESN'T WORK YET!

-- > instance Quote (Value, Value) Normal where
-- >     quote (v@(MR (RdBind n (B Lambda _) _)),
-- >                 (MR (RdBind _ (B Pi ty) (Kr (f,w)))))
-- >         = (MR (RdBind n (B Lambda (quote ty))
-- >                (Sc (quote ((apply (VG []) (v) v0),
-- >                      (f w v0))))))
-- >       where v0 = MB (BV 0, ty) Empty
-- >     quote (v, (MR (RdBind n (B Pi ty) (Kr (f,w)))))
-- >         = (MR (RdBind n (B Lambda (quote ty))
-- >                (Sc (quote ((apply (VG []) (weaken (Wk 1) v) v0),
-- >                      (f w v0))))))
-- >       where v0 = MB (BV 0, ty) Empty
-- >     quote ((MB (bl,ty) sp), _)
-- >         = MB (quote bl, quote ty) (fst (qspine sp))
-- >        where qspine Empty = (Empty, ty)
-- >              qspine (Snoc sp v)
-- >                  | (sp', MR (RdBind _ (B Pi t) (Kr (f,w)))) <- qspine sp
-- >                      = (Snoc sp' (quote (v,weaken (Wk 1) t)),
-- >                           f w v)
-- >                  | (sp', t) <- qspine sp
-- >                      = (Snoc sp' (quote v), t)
-- > --error $ show (forget ((quote t)::Normal))
-- >              v0 t = MB (BV 0, t) Empty
-- >     quote (v, t) = quote v

> instance Forget Normal (TT Name) where
>     forget (MB (b, _) sp) = makeApp (forget b) (fmap forget sp)
>     forget (MR r) = forget r

> instance Forget (Blocked Scope) (TT Name) where
>     forget (BCon t n j) = Con t n j
>     forget (BTyCon n j) = TyCon n j
>     forget (BElim e n) = Elim n
>     forget (BPatDef p n) = P n
>     forget (BRec n v) = P n
>     forget (BPrimOp f n) = P n
>     forget (BP n) = P n
>     forget (BV i) = V i
>     forget (BEval t ty) = Stage (Eval (forget t) (forget ty))
>     forget (BEscape t ty) = Stage (Escape (forget t) (forget ty))

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
> normalise g (Ind t) = Ind (forget (quote (nf g (VG []) [] False t)::Normal))

WARNING: quotation to eta long normal form doesn't work yet.

> etaNormalise :: Gamma Name -> (Indexed Name, Indexed Name) -> (Indexed Name)
> etaNormalise g (Ind tm, Ind ty) = undefined

-- >     let vtm = (nf g (VG []) [] False tm)
-- >         vty = (nf g (VG []) [] False ty) in
-- >       Ind (forget (quote (vtm, vty)::Normal))

> convNormalise :: Gamma Name -> (Indexed Name) -> (Indexed Name)
> convNormalise g (Ind t)
>     = Ind (forget (quote (nf g (VG []) [] True t)::Normal))

> normaliseEnv :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> normaliseEnv env g t
>     = normalise (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g)
>             = addenv xs (Gam (Map.insert n (G (Fun [] (Ind v)) (Ind ty) defplicit) g))
>         addenv (_:xs) g = addenv xs g

> convNormaliseEnv :: Env Name -> Gamma Name -> Indexed Name -> Indexed Name
> convNormaliseEnv env g t
>     = convNormalise (addenv env g) t
>   where addenv [] g = g
>         addenv ((n,B (Let v) ty):xs) (Gam g)
>             = addenv xs (Gam (Map.insert n (G (Fun [] (Ind v)) (Ind ty) defplicit) g))
>         addenv (_:xs) g = addenv xs g

     = Ind (forget (quote (nf g (VG (valenv env [])) t)::Normal))
    where valenv [] env = trace (show (map forget ((map quote env)::[Normal]))) $ env
          valenv ((n,B (Let v) ty):xs) env = valenv xs ((eval env v):env)
          valenv ((n,B _ ty):xs) env = valenv xs ((MB (BP n) Empty):env)
          eval env v = nf g (VG env) v

-- > natElim :: ElimRule
-- > natElim (Snoc args@(Snoc (Snoc (Snoc Empty phi) phiZ) phiS)
-- >            (MR (RCon 0 (UN "O") sp)))
-- >      = return phiZ
-- > natElim (Snoc args@(Snoc (Snoc (Snoc Empty phi) phiZ) phiS)
-- >            (MR (RCon 1 (UN "S") (Snoc Empty n))))
-- >      = return (apply (VG []) (apply (VG []) phiS n)
-- >                  (apply (VG []) rec n))
-- >    where rec = (MB (BElim natElim (UN "nateElim")) args)
-- > natElim _ = Nothing

-- > genElim :: Int -> Int -> [(Name,Ctxt -> Value)] -> ElimRule
-- > genElim arity con red sp
-- >   | size sp < arity = Nothing
-- >   | otherwise = case (sp??con) of
-- >        (MR (RCon t n args)) ->
-- >              do v <- lookup n red
-- >                 let ctx = VG $ (makectx args)++(makectx (lose con sp))
-- >                 return $ v ctx
-- >        _ -> Nothing
-- >   where makectx (Snoc xs x) = x:(makectx xs)
-- >         makectx Empty = []


====================== Functors for contexts ===============================

 instance Functor Gamma where
     fmap f (Gam xs) = let xsList = Map.toAscList xs
                           mList = fmap (\ (x,y) -> (f x,fmap f y)) xsList in
                           Gam (Map.fromAscList mList)

 instance Functor Gval where
     fmap f (G g i p) = G (fmap f g) (fmap f i) p

> instance Functor Global where
>     fmap f (Fun opts n) = Fun opts $ fmap f n
>     fmap f (ElimRule e) = ElimRule e
>     fmap f (DCon t i) = DCon t i
>     fmap f (TCon i (Elims en cn cons))
>              = TCon i (Elims (f en) (f cn) (fmap f cons))


> arity :: Gamma Name -> Indexed Name -> Int
> arity g t = ca (normalise g t)
>    where ca (Ind t) = ca' t
>          ca' (Bind _ (B Pi _) (Sc r)) = 1+(ca' r)
>          ca' _ = 0