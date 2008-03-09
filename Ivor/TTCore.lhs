> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.TTCore where

> import Ivor.Gadgets
> import Ivor.Constant

> import List
> import Char
> import Control.Monad.State
> import Data.Typeable
> import Debug.Trace

Raw terms are those read in directly from the user, and may be badly typed.
(Need to add marked up terms for optimisation).

> data Raw
>     = Var Name
>     | RApp Raw Raw
>     | RBind Name (Binder Raw) Raw
>     | forall c.(Constant c) => RConst !c
>     | RStar
>     | RInfer -- Term to be inferred by the typechecker
>     | RMeta Name -- a metavariable, to be implemented separately
>     | RLabel Raw RComputation
>     | RCall RComputation Raw
>     | RReturn Raw
>     | RAnnot String -- Debugging hack
>     | RStage RStage

> data RComputation = RComp Name [Raw]
>   deriving Eq

> data RStage = RQuote Raw
>             | RCode Raw
>             | REval Raw 
>             | REscape Raw
>   deriving Eq

TT represents terms in the core type theory, parametrised by the 
representation of the names

> data TT n
>     = P n
>     | V Int
>     | Con Int n Int -- Tag, name and arity
>     | TyCon n Int  -- Name and arity
>     | Elim n
>     | App (TT n) (TT n)
>     | Bind n (Binder (TT n)) (Scope (TT n))
>     | Proj n Int (TT n) -- Projection in iota schemes (carries type name)
>     | Label (TT n) (Computation n)
>     | Call (Computation n) (TT n) 
>     | Return (TT n)
>     | forall c. Constant c => Const !c
>     | Star
>     | Stage (Stage n)

> data Computation n = Comp n [TT n]

Stage gives staging annotations

> data Stage n = Quote (TT n)
>              | Code (TT n)
>              | Eval (TT n) (TT n) -- term, type
>              | Escape (TT n) (TT n) -- term, type
>  deriving Show

Constants

> class (Typeable c, Show c, Eq c) => Constant c where
>     constType :: c -> TT Name

> newtype Scope n = Sc n
>    deriving (Show, Eq)

> data Binder n = B (Bind n) n
>    deriving (Show, Eq)

> data Bind n 
>     = Lambda
>     | Pi
>     | Let n
>     | Hole
>     | Guess n
>     | Pattern n
>     | MatchAny
>    deriving (Show, Eq)

Local environments

> type Env n = [(n,Binder (TT n))]

Separate types for de Bruijn indexed terms and de Bruijn levelled terms

> newtype Levelled n = Lev (TT n) deriving Eq
> newtype Indexed n = Ind (TT n) deriving Eq

Pattern represents the patterns used to define iota schemes.

> data Pattern n =
>	 PVar n  -- Variable
>      | PCon Int n n [Pattern n] -- Constructor, with tag and type
>      | forall c.(Constant c) => PConst !c
>      | PMarkCon n [Pattern n] -- Detagged constructor
>      | PTerm -- Presupposed term (don't care what it is)
>      | PMark n  -- Marked variable

> instance Show n => Show (Pattern n) where
>     show (PVar n) = show n
>     show (PCon t n ty ts) = show n ++ show ts
>     show (PConst c) = show c
>     show (PMarkCon n ts) = show n ++ show ts
>     show PTerm = "_"
>     show (PMark n) = "[" ++ show n ++ "]"

> instance Eq n => Eq (Pattern n) where
>     (==) (PVar x) (PVar y) = x == y
>     (==) (PCon t1 n1 ty1 ts1) (PCon t2 n2 ty2 ts2) = t1 == t2 &&
>                                                      n1 == n2 &&
>                                                      ty1 == ty2 &&
>                                                      ts1 == ts2
>     (==) (PConst x) (PConst y) = case cast x of
>                                     Just x' -> x' == y
>                                     _ -> False
>     (==) (PMarkCon n1 ts1) (PMarkCon n2 ts2) = n1 == n2 && ts1 == ts2
>     (==) PTerm PTerm = True
>     (==) (PMark x) (PMark y) = x == y
>     (==) _ _ = False

      {- | forall c. Constant c => PConst c -- Constant (don't think it makes sense) -}

> instance Eq n => Ord (Pattern n) where
>     compare (PCon x _ _ _) (PCon y _ _ _) = compare x y
>     compare _ _ = EQ -- Don't care!

UN covers names defined by users, MN covers names invented by the system.
This keeps both namespaces separate.

> data Name 
>     = UN String
>     | MN (String,Int) 
>   deriving Eq

Data declarations and pattern matching

> data RawScheme = RSch [Raw] Raw
>   deriving Show

> data Scheme n = Sch [Pattern n] (Indexed n)
>         deriving Show

> type PMRaw = RawScheme

For equality of patterns, we're only interested in whether the LHS are
equal. This is so that we can easily filter out overlapping cases when
generating cases for coverage/type checking. Checking for overlapping
is dealt with later.

> instance Eq PMRaw where
>     (==) (RSch ps r) (RSch ps' r') = ps == ps'

> type PMDef n = Scheme n

> data PMFun n = PMFun Int -- arity
>                      [PMDef n] -- patterns
>    deriving Show

====================== Functors ===============================

> instance Functor Scope where
>     fmap f (Sc x) = Sc (f x)

> instance Functor Binder where
>     fmap f (B b x) = B (fmap f b) (f x)

> instance Functor Bind where
>     fmap f Lambda = Lambda
>     fmap f Pi = Pi
>     fmap f (Let x) = Let (f x)
>     fmap f Hole = Hole
>     fmap f (Guess x) = Guess (f x)
>     fmap f (Pattern x) = Pattern (f x)
>     fmap f MatchAny = MatchAny

> instance Functor TT where
>     fmap f (P x) = P (f x)
>     fmap f (V i) = V i
>     fmap f (Con t x i) = Con t (f x) i
>     fmap f (TyCon x i) = TyCon (f x) i
>     fmap f (Elim x) = Elim (f x)
>     fmap f (App tf a) = App (fmap f tf) (fmap f a)
>     fmap f (Bind n b sc) = Bind (f n) (fmap (fmap f) b) (fmap (fmap f) sc)
>     fmap f (Proj n i x) = Proj (f n) i (fmap f x)
>     fmap f (Const x) = Const x
>     fmap f (Label t c) = Label (fmap f t) (fmap f c)
>     fmap f (Call c t) = Call (fmap f c) (fmap f t)
>     fmap f (Return t) = Return (fmap f t)
>     fmap f (Stage t) = Stage (fmap f t)
>     fmap f Star = Star

> instance Functor Stage where
>     fmap f (Quote t) = Quote (fmap f t)
>     fmap f (Code t) = Code (fmap f t)
>     fmap f (Eval t ty) = Eval (fmap f t) (fmap f ty)
>     fmap f (Escape t ty) = Escape (fmap f t) (fmap f ty)

> sLift :: (TT a -> TT b) -> Stage a -> Stage b
> sLift f (Quote t) = Quote (f t)
> sLift f (Code t) = Code (f t)
> sLift f (Eval t ty) = Eval (f t) (f ty)
> sLift f (Escape t ty) = Escape (f t) (f ty)

> sLiftf :: (TT a -> b) -> Stage a -> b
> sLiftf f (Quote t) = f t
> sLiftf f (Code t) = f t
> sLiftf f (Eval t ty) = f t
> sLiftf f (Escape t ty) = f t

> sLiftM :: Monad m => (TT a -> m (TT b)) -> Stage a -> m (Stage b)
> sLiftM f (Quote t) = do x <- f t
>                         return $ Quote x
> sLiftM f (Code t) = do x <- f t
>                        return $ Code x
> sLiftM f (Eval t ty) = do x <- f t
>                           xty <- f ty
>                           return $ Eval x xty
> sLiftM f (Escape t ty) = do x <- f t
>                             xty <- f ty
>                             return $ Escape x xty

> instance Functor Computation where
>     fmap f (Comp n ts) = Comp (f n) (fmap (fmap f) ts)

> instance Functor Indexed where
>     fmap f (Ind t) = Ind $ fmap f t

> instance Functor Levelled where
>     fmap f (Lev t) = Lev $ fmap f t

====================== Gadgets for TT =============================

Do something hairy to all the Vs in a TT term. Kind of like fmap, only on
the variable numbers rather than the names.

Each V is processed with a function taking the context and the index.

> vapp :: (([n],Int) -> (TT n)) -> TT n -> TT n
> vapp f t = v' [] t
>   where
>     v' ctx (V i) = f (ctx,i)
>     v' ctx (App f' a) = (App (v' ctx f') (v' ctx a))
>     v' ctx (Bind n b (Sc sc)) = (Bind n (fmap (v' ctx) b) 
>			          (Sc (v' (n:ctx) sc)))
>     v' ctx (Proj n i x) = Proj n i (v' ctx x)
>     v' ctx (Label t (Comp n cs)) 
>         = Label (v' ctx t) (Comp n (fmap (v' ctx) cs))
>     v' ctx (Call (Comp n cs) t) 
>         = Call (Comp n (fmap (v' ctx) cs)) (v' ctx t)
>     v' ctx (Return t) = Return (v' ctx t)
>     v' ctx (Stage t) = Stage (sLift (v' ctx) t)
>     v' ctx x = x

> indexise :: Levelled n -> Indexed n
> indexise (Lev t) = Ind $ vapp (\ (ctx,i) -> V (i-((length ctx)-1))) t

> levelise :: Indexed n -> Levelled n
> levelise (Ind t) = Lev $ vapp (\ (ctx,i) -> V ((length ctx)-i-1)) t

Same, but for Ps

> papp :: (n -> (TT n)) -> TT n -> TT n
> papp f t = v' t
>   where
>     v' (P n) = f n
>     v' (V i) = V i
>     v' (App f' a) = (App (v' f') (v' a))
>     v' (Bind n b (Sc sc)) = (Bind n (fmap (v') b) 
>			          (Sc (v' sc)))
>     v' (Proj n i x) = Proj n i (v' x)
>     v' (Label t (Comp n cs)) 
>         = Label (v' t) (Comp n (fmap (v') cs))
>     v' (Call (Comp n cs) t) 
>         = Call (Comp n (fmap (v') cs)) (v' t)
>     v' (Return t) = Return (v' t)
>     v' (Stage t) = Stage (sLift (v') t)
>     v' x = x

FIXME: This needs to rename all duplicated binder names first, otherwise
we get a duff term when we go back to the indexed version.

> makePs :: TT Name -> TT Name
> makePs t = let t' = evalState (uniqifyAllState t) [] in
>                 vapp (\ (ctx,i) -> P (traceIndex ctx i "makePsEnv")) t' 
>                            --if (i<length ctx) then P (ctx!!i)
>                              --           else V i) t'

> makePsEnv env t = let t' = evalState (uniqifyAllState t) env in
>                       vapp (\ (ctx,i) -> P (traceIndex ctx i "makePsEnv")) t'


> uniqifyAllState :: TT Name -> State [Name] (TT Name)
> uniqifyAllState (Bind n b (Sc sc)) =
>     do names <- get
>        let n' = uniqify n names
>        put $ nub (n':names)
>        b' <- uniqifyAllStateB b
>        sc' <- uniqifyAllState sc
>        return (Bind n' b' (Sc sc'))
> uniqifyAllState (App f a) = 
>     do f' <- uniqifyAllState f
>        a' <- uniqifyAllState a
>        return (App f' a')
> uniqifyAllState (Proj n i t) = 
>     do t' <- uniqifyAllState t
>        return (Proj n i t')
> uniqifyAllState (Label t c) =
>     do t' <- uniqifyAllState t
>        c' <- uniqifyAllStateC c
>        return (Label t' c')
> uniqifyAllState (Call c t) =
>     do t' <- uniqifyAllState t
>        c' <- uniqifyAllStateC c
>        return (Call c' t')
> uniqifyAllState (Return t) = 
>     do t' <- uniqifyAllState t
>        return (Return t')
> uniqifyAllState (Stage t) =
>     do t' <- sLiftM uniqifyAllState t
>        return (Stage t')
> uniqifyAllState x = return $ x

> uniqifyAllStateB (B Lambda ty) = 
>     do ty' <- uniqifyAllState ty
>        return (B Lambda ty')
> uniqifyAllStateB (B Pi ty) = 
>     do ty' <- uniqifyAllState ty
>        return (B Pi ty')
> uniqifyAllStateB (B Hole ty) = 
>     do ty' <- uniqifyAllState ty
>        return (B Hole ty')
> uniqifyAllStateB (B (Let v) ty) = 
>     do ty' <- uniqifyAllState ty
>        v' <- uniqifyAllState v
>        return (B (Let v') ty')
> uniqifyAllStateB (B (Guess v) ty) = 
>     do ty' <- uniqifyAllState ty
>        v' <- uniqifyAllState v
>        return (B (Guess v') ty')
> uniqifyAllStateB (B (Pattern v) ty) = 
>     do ty' <- uniqifyAllState ty
>        v' <- uniqifyAllState v
>        return (B (Pattern v') ty')
> uniqifyAllStateB (B MatchAny ty) = 
>     do ty' <- uniqifyAllState ty
>        return (B MatchAny ty')
> uniqifyAllStateC (Comp n cs) =
>     do cs' <- mapM uniqifyAllState cs
>        return (Comp n cs')


Take a term with explicit names and convert it to a term with 
de Bruijn indices

> finalise :: Eq n => Indexed n -> Indexed n
> finalise (Ind tm) = Ind (pv [] tm)
>   where
>    pv env (P n) | Just i <- lookupidx 0 n env = V i
>                 | otherwise = P n
>    pv env (App f a) = App (pv env f) (pv env a)
>    pv env (Proj n i t) = Proj n i (pv env t)
>    pv env (Bind n b@(B _ ty) (Sc t)) 
>        = Bind n (fmap (pv env) b) (Sc (pv ((n,(pv env ty)):env) t))
>    pv env (Label t (Comp n cs)) 
>       = Label (pv env t) (Comp n (fmap (pv env) cs))
>    pv env (Call (Comp n cs) t) 
>       = Call (Comp n (fmap (pv env) cs)) (pv env t)
>    pv env (Return t) = Return (pv env t)
>    pv env (Stage t) = Stage (sLift (pv env) t)
>    pv env x = x
>    
>    lookupidx i n ((x,_):xs) | n==x = Just i
>                             | otherwise = lookupidx (i+1) n xs
>    lookupidx i n [] = Nothing

Check the purity of a term; a term is pure iff it has no holes.

> pure :: TT Name -> Bool
> pure (Bind _ (B b ty) (Sc sc)) = purebind b && pure ty && pure sc
> pure (App f a) = pure f && pure a
> pure (Proj _ _ t) = pure t
> pure (Label t (Comp n cs)) = pure t && and (map pure cs)
> pure (Call (Comp n cs) t) = pure t && and (map pure cs)
> pure (Return t) = pure t
> pure (Stage t) = sLiftf pure t
> pure _ = True
>
> purebind Hole = False -- Seems a bit OTT to use a type class just for this...
> purebind (Guess _) = False
> purebind (Let t) = pure t
> purebind _ = True

Map a function across all binders in a term

> binderMap :: (Name -> Bind (TT Name) -> TT Name -> a) -> TT Name -> [a]
> binderMap f (Bind n (B b@(Let v) ty) (Sc sc))
>     = (f n b ty):(binderMap f v) ++ (binderMap f ty) ++ (binderMap f sc)
> binderMap f (Bind n (B b@(Guess v) ty) (Sc sc))
>     = (f n b ty):(binderMap f v) ++ (binderMap f ty) ++ (binderMap f sc)
> binderMap f (Bind n (B b@(Pattern v) ty) (Sc sc))
>     = (f n b ty):(binderMap f v) ++ (binderMap f ty) ++ (binderMap f sc)
> binderMap f (Bind n (B b ty) (Sc sc))
>     = (f n b ty):(binderMap f ty) ++ (binderMap f sc)
> binderMap bf (App f a) = binderMap bf f ++ binderMap bf a
> binderMap f (Proj _ _ t) = binderMap f t
> binderMap f (Label t (Comp n cs)) = binderMap f t ++
>                                     concat (fmap (binderMap f) cs)
> binderMap f (Call (Comp n cs) t) = concat (fmap (binderMap f) cs) ++
>                                    binderMap f t
> binderMap f (Return t) = binderMap f t
> binderMap f (Stage t) = sLiftf (binderMap f) t
> binderMap f _ = []

Substitute a term into V 0 in the scope (and weaken other indices)
I think this works! But de Bruijn index mangling breaks my brain, so
maybe find a better way, or think carefully about why this is okay...

> subst :: TT n -> Scope (TT n) -> TT n
> subst tm (Sc x) = vapp weakenv $ vapp subv x
>   where subv (xs,i) | i == length xs = (vinc tm)
>                     | otherwise = V i
>         weakenv (xs,i) | i > length xs = V (i-1)
>                        | otherwise = V i
>         vinc (V n) = V (n+1) -- So that we weakenv it correctly
>         vinc x = x

Return all the names used in a scope

> getNames :: Eq n => Scope (TT n) -> [n]
> getNames (Sc x) = nub $ p' x where
>     p' (P x) = [x]
>     p' (App f' a) = (p' f')++(p' a)
>     p' (Bind n b (Sc sc)) 
>      | scnames <- p' sc = (scnames \\ [n]) ++ pb' b
>     p' (Proj _ i x) = p' x
>     p' (Label t (Comp n cs)) = p' t ++ concat (map p' cs)
>     p' (Call (Comp n cs) t) = concat (map p' cs) ++ p' t
>     p' (Return t) = p' t
>     p' (Stage t) = sLiftf p' t
>     p' x = []
>     pb' (B (Let v) ty) = p' v ++ p' ty
>     pb' (B (Guess v) ty) = p' v ++ p' ty
>     pb' (B (Pattern v) ty) = p' v ++ p' ty
>     pb' (B _ ty) = p' ty

Return all the bound names used in a scope

> getBoundNames :: Eq n => Scope (TT n) -> [n]
> getBoundNames (Sc x) = nub $ p' x where
>     p' (P x) = []
>     p' (App f' a) = (p' f')++(p' a)
>     p' (Bind n b (Sc sc)) = n:(p' sc) ++ pb' b
>     p' (Proj _ i x) = p' x
>     p' (Label t (Comp n cs)) = p' t ++ concat (map p' cs)
>     p' (Call (Comp n cs) t) = concat (map p' cs) ++ p' t
>     p' (Return t) = p' t
>     p' (Stage t) = sLiftf p' t
>     p' x = []
>     pb' (B (Let v) ty) = p' v ++ p' ty
>     pb' (B (Guess v) ty) = p' v ++ p' ty
>     pb' (B (Pattern v) ty) = p' v ++ p' ty
>     pb' (B _ ty) = p' ty

The following gadgets expect a fully explicitly named term, rather than
with de Bruijn indices or levels. We need a newtype Named n.

> substName :: (Show n, Eq n) => n -> TT n -> Scope (TT n) -> TT n
> substName p tm (Sc x) = p' x where
>     p' (P x) | x == p = tm
>     p' (App f' a) = (App (p' f') (p' a))
>     p' (Bind n b (Sc sc)) = (Bind n (fmap p' b) (Sc (p' sc)))
>      --   | n == p = (Bind n (fmap p' b) (Sc sc))
>      --   | otherwise 
>     p' (Proj n i x) = Proj n i (p' x)
>     p' (Label t (Comp n cs)) = Label (p' t) (Comp n (map p' cs))
>     p' (Call (Comp n cs) t) = Call (Comp n (map p' cs)) (p' t)
>     p' (Return t) = Return (p' t)
>     p' (Stage t) = Stage (sLift p' t)
>     p' x = x

Look for a specific term and replace it.
Probably hopelessly inefficient.

> substTerm :: (Show n, Eq n) => TT n -> TT n -> Scope (TT n) -> TT n
> substTerm p tm (Sc x) = p' x where
>     p' x | x == p = tm
>     p' (App f' a) = (App (p' f') (p' a))
>     p' (Bind n b (Sc sc)) = (Bind n (fmap p' b) (Sc (p' sc)))
>      --   | n == p = (Bind n (fmap p' b) (Sc sc))
>      --   | otherwise 
>     p' (Proj n i x) = Proj n i (p' x)
>     p' (Label t (Comp n cs)) = Label (p' t) (Comp n (map p' cs))
>     p' (Call (Comp n cs) t) = Call (Comp n (map p' cs)) (p' t)
>     p' (Return t) = Return (p' t)
>     p' (Stage t) = Stage (sLift p' t)
>     p' x = x

> getSc (Sc x) = x

Apply a function (non-recursively) to every sub term.

> mapSubTerm :: (TT Name -> TT Name) -> TT Name -> TT Name
> mapSubTerm f = mst where
>    mst (App ff s) = App (f ff) (f s)
>    mst (Bind x b (Sc sc)) = Bind x (fmap f b) (Sc (f sc))
>    mst (Proj n i ty) = Proj n i (f ty)
>    mst (Stage t) = Stage (sLift f t)
>    mst x = x 

Get the arguments of an application

> getArgs :: TT Name -> [TT Name]
> getArgs (App f a) = getArgs f ++ [a]
> getArgs _ = []

Get the function being applied in an application

> getFun :: TT Name -> TT Name
> getFun (App f a) = getFun f
> getFun x = x

Get the expected arguments of a function type

> getExpected :: TT Name -> [(Name,TT Name)]
> getExpected (Bind n (B Pi ty) (Sc sc)) = (n,ty):(getExpected sc)
> getExpected _ = []

Get the return type of a function type

> getReturnType :: TT Name -> TT Name
> getReturnType (Bind n (B Pi ty) (Sc sc)) = getReturnType sc
> getReturnType x = x

Make a name unique in the given environment

> uniqify :: Name -> [Name] -> Name
> uniqify x env | x `elem` env = uniqify (mangleName x) env
>               | otherwise = x

x -> x0, x1 -> x2, etc. Increments an index at the end of a name, in order
to generate a new and hopefully unique name.

> mangleName :: Name -> Name
> mangleName (MN (n,i)) = MN (n,i+1)
> mangleName (UN n) = UN (incName n)
>    where incName x | (num, name) <- span isDigit (reverse x)
>                        = (reverse name)++show (inc num)
>
>          inc :: String -> Int
>          inc "" = 0
>          inc xs = (read (reverse xs)) + 1

Bind a list of things

> bind :: Bind (TT Name) -> [(Name,TT Name)] -> Scope (TT Name) -> TT Name
> bind binder [] sc = getSc sc
> bind binder ((n,ty):xs) sc = Bind n (B binder ty) (Sc (bind binder xs sc))

Apply a function to a list of arguments

> appArgs :: TT n -> [TT n] -> TT n
> appArgs f [] = f
> appArgs f (x:xs) = appArgs (App f x) xs

====================== Show instances =============================

> instance Show Name where
>     show = forget

> instance Show n => Show (TT n) where
>     show x = forget (forget x)

> instance Show Raw where
>     show = forget

> instance Show n => (Show (Levelled n)) where
>     show = show.indexise

> instance Show n => (Show (Indexed n)) where
>     show (Ind t) = show t

===================== Eq instances ================================

> instance Eq Raw where
>     (==) (Var x) (Var y) = x==y
>     (==) (RApp f a) (RApp f' a') = f==f' && a==a'
>     (==) (RBind n b sc) (RBind n' b' sc') = n==n' && b==b' && sc==sc'
>     (==) (RConst x) (RConst y) = case cast x of 
>                                    Just x' -> x'==y
>                                    Nothing -> False
>     (==) RStar RStar = True
>     (==) (RLabel t (RComp n cs)) (RLabel t' (RComp n' cs')) =
>         t==t' && n==n' && cs == cs'
>     (==) (RCall (RComp n cs) t) (RCall (RComp n' cs') t') =
>         t==t' && n==n' && cs == cs'
>     (==) (RReturn t) (RReturn t') = t == t'
>     (==) (RStage t) (RStage t') = t == t'
>     (==) RInfer RInfer = True
>     (==) (RMeta x) (RMeta x') = x == x'
>     (==) _ _ = False

> instance Eq n => Eq (TT n) where
>     (==) (P x) (P y) = x==y
>     (==) (V i) (V j) = i==j
>     (==) (Con t x i) (Con t' y j) = x==y
>     (==) (TyCon x i) (TyCon y j) = x==y
>     (==) (Elim x) (Elim y) = x==y
>     (==) (App f a) (App f' a') = f==f' && a==a'
>     (==) (Bind _ b sc) (Bind _ b' sc') = b==b' && sc==sc'
>     (==) (Proj _ i x) (Proj _ j y) = i==j && x==y
>     (==) (Const x) (Const y) = case cast x of 
>                                   Just x' -> x'==y
>                                   Nothing -> False
>     (==) Star Star = True
>     (==) (Label t (Comp n cs)) (Label t' (Comp n' cs')) =
>         t==t' -- && n==n' && cs == cs'
>     (==) (Call (Comp n cs) t) (Call (Comp n' cs') t') =
>         t==t' -- && n==n' && cs == cs'
>     (==) (Return t) (Return t') = t == t'
>     (==) (Stage t) (Stage t') = t == t'
>     (==) _ _ = False

> instance Eq n => Eq (Stage n) where
>     (==) (Quote t) (Quote t') = t == t'
>     (==) (Code t) (Code t') = t == t'
>     (==) (Eval t _) (Eval t' _) = t == t'
>     (==) (Escape t _) (Escape t' _) = t == t'
>     (==) _ _ = False

===================== Forgetful maps ==============================

> instance Forget Name String where
>     forget (UN n) = n
>     forget (MN ("INFER",i)) = "y"++show i
>     forget (MN ("T",i)) = "z"++show i
>     forget (MN (x,i)) = x ++ "[" ++ show i ++ "]"

> instance Forget Raw String where
>     forget x = fPrec 10 x where
>       fPrec :: Int -> Raw -> String
>       fPrec _ (Var n) = forget n
>       fPrec x (RApp f a) = bracket x 1 $ fPrec 1 f ++ " " ++ fPrec 0 a
>       fPrec x (RBind n (B Lambda t) sc) = bracket x 2 $
>           "["++forget n ++":"++fPrec 10 t++"]" ++ fPrec 10 sc
>       fPrec x (RBind n (B Pi t) sc) 
>           | nameOccurs n sc = bracket x 2 $
>              "("++forget n ++":"++fPrec 10 t++") -> " ++ fPrec 10 sc
>           | otherwise = bracket x 2 $
>              (fPrec 1 t) ++" -> " ++ fPrec 10 sc
>       fPrec x (RBind n (B (Let v) t) sc) = bracket x 2 $
>           "let "++forget n ++":"++ fPrec 10 t
>                 ++"=" ++ fPrec 10 v ++ " in " ++ fPrec 10 sc
>       fPrec x (RBind n (B Hole t) sc) = bracket x 2 $
>           "?"++forget n ++":"++fPrec 10 t++"." ++ fPrec 10 sc
>       fPrec x (RBind n (B (Guess v) t) sc) = bracket x 2 $
>           "try "++forget n ++":"++fPrec 10 t
>                 ++"=" ++ fPrec 10 v ++ " in " ++ fPrec 10 sc
>       fPrec x (RBind n (B (Pattern v) t) sc) = bracket x 2 $
>           "patt "++forget n ++":"++fPrec 10 t
>                 ++"=" ++ fPrec 10 v ++ " in " ++ fPrec 10 sc
>       fPrec x (RBind n (B MatchAny t) sc) = bracket x 2 $
>           "patt "++forget n ++":"++fPrec 10 t ++ " in " ++ fPrec 10 sc
>       fPrec _ (RLabel t c) =
>           "< "++fPrec 10 t++" : "++fcomp c++" >"
>       fPrec x (RCall c t) = bracket x 3 $
>           "call < " ++ fcomp c ++ " > "++ fPrec 0 t
>       fPrec _ (RReturn t) = "return " ++ fPrec 0 t
>       fPrec _ (RStage (RQuote t)) = "{'" ++ fPrec 10 t ++ "}"
>       fPrec _ (RStage (RCode t)) = "{{" ++ fPrec 10 t ++ "}}"
>       fPrec _ (RStage (REval t)) = "!" ++ fPrec 0 t
>       fPrec _ (RStage (REscape t)) = "~" ++ fPrec 0 t
>       fPrec _ (RConst x) = show x
>       fPrec _ (RStar) = "*"
>       fPrec _ (RInfer) = "_"
>       fPrec _ (RMeta n) = "?"++forget n
>       fPrec _ (RAnnot t) = t
>       bracket outer inner str | inner>outer = "("++str++")"
>                               | otherwise = str

>       fcomp (RComp n cs) = forget n ++ showargs cs
>           where showargs [] = ""
>                 showargs (x:xs) = " " ++ fPrec 0 x ++ showargs xs

> instance Forget RStage String where
>     forget (RQuote x) = "{'" ++ forget x ++ "}"
>     forget (RCode x) = "{{" ++ forget x ++ "}}"
>     forget (REval x) = "{!" ++ forget x ++ "}"
>     forget (REscape x) = "{~" ++ forget x ++ "}"

> instance Show n => Forget (Indexed n) Raw where
>     forget (Ind t) = forget t

> instance Show n => Forget (Levelled n) Raw where
>     forget (Lev t) = forget t

> instance Show n => Forget (TT n) Raw where
>     forget t = forgetTT (vapp showV t)
>      where
>        showV (ctx,i) | i < length ctx = P (ctx!!i)
>	               | otherwise = V i
>        forgetTT (P x) = Var $ UN (show x)
>        forgetTT (V i) = RAnnot $ "v" ++ (show i)
>        forgetTT (Con t x i) = Var $ UN (show x)
>        forgetTT (TyCon x i) = Var $ UN (show x)
>        forgetTT (Elim x) = Var $ UN (show x)
>        forgetTT (App f a) = RApp (forgetTT f) (forgetTT a)
>        forgetTT (Bind n (B Lambda t) (Sc sc)) =
>                    (RBind (UN (show n)) (B Lambda (forget t)) (forget sc))
>        forgetTT (Bind n (B Pi t) (Sc sc)) =
>                    (RBind (UN (show n)) (B Pi (forget t)) (forget sc))
>        forgetTT (Bind n (B MatchAny t) (Sc sc)) =
>                    (RBind (UN (show n)) (B MatchAny (forget t)) (forget sc))
>        forgetTT (Bind n (B (Let v) t) (Sc sc)) =
>                    (RBind (UN (show n)) (B (Let (forget v)) (forget t))
>                      (forget sc))
>        forgetTT (Bind n (B Hole t) (Sc sc)) =
>                    (RBind (UN (show n)) (B Hole (forget t)) (forget sc))
>        forgetTT (Bind n (B (Guess v) t) (Sc sc)) =
>                    (RBind (UN (show n)) (B (Guess (forget v)) (forget t))
>                      (forget sc))
>        forgetTT (Bind n (B (Pattern v) t) (Sc sc)) =
>                    (RBind (UN (show n)) (B (Pattern (forget v)) (forget t))
>                      (forget sc))
>        forgetTT (Proj n i t) = RAnnot $ (show t)++"!"++(show i)++":"++show n
>        forgetTT (Label t (Comp n cs)) = RLabel (forgetTT t)
>                                          (RComp (UN $ show n)
>                                             (map forgetTT cs))
>        forgetTT (Call (Comp n cs) t) = RCall (RComp (UN $ show n)
>                                               (map forgetTT cs))
>                                                 (forgetTT t)
>        forgetTT (Return t) = RReturn (forgetTT t)
>        forgetTT (Stage t) = RStage (forget t)
>        forgetTT (Const x) = RConst x
>        forgetTT Star = RStar

> instance Show n => Forget (Stage n) RStage where
>     forget (Code x) = RCode (forget x)
>     forget (Quote x) = RQuote (forget x)
>     forget (Eval x _) = REval (forget x)
>     forget (Escape x _) = REscape (forget x)

> testid = (Bind (UN "x") (B Lambda Star) (Sc (V 0)))
> testterm = (App testid Star)

Some handy gadgets for Raw terms

> mkapp f [] = f
> mkapp f (x:xs) = mkapp (RApp f x) xs

> getargnames (RBind n _ sc) = n:(getargnames sc)
> getargnames _ = []

> getappargs (RApp f a) = getappargs f ++ [a]
> getappargs _ = []

> getappfun (RApp f a) = getappfun f
> getappfun x = x

> getrettype (RBind n (B Pi _) sc) = getrettype sc
> getrettype x = x

> nameOccurs x (Var n) | x == n = True
>                      | otherwise = False
> nameOccurs x (RApp f a) = nameOccurs x f || nameOccurs x a
> nameOccurs x (RBind n b sc) 
>     | x == n = False
>     | otherwise = occBind x b || nameOccurs x sc
> nameOccurs x (RLabel r comp) = nameOccurs x r || occComp x comp
> nameOccurs x (RCall comp r)  = nameOccurs x r || occComp x comp
> nameOccurs x (RReturn r) = nameOccurs x r
> nameOccurs x (RStage s) = occStage x s
> nameOccurs x _ = False

> occComp x (RComp _ rs) = or $ map (nameOccurs x) rs
> occBind x (B (Let v) t) = nameOccurs x v || nameOccurs x t
> occBind x (B _ t) = nameOccurs x t
> occStage x (RQuote r) = nameOccurs x r
> occStage x (RCode r) = nameOccurs x r
> occStage x (REval r) = nameOccurs x r
> occStage x (REscape r) = nameOccurs x r


> debugTT t = show (forgetTT (vapp showV t))
>      where
>        showV (ctx,i) | i < length ctx = P (UN ("{v}"++show i))
>	               | otherwise = V i
>        forgetTT (P x) = Var $ UN (show x)
>        forgetTT (V i) = RAnnot $ "v" ++ (show i)
>        forgetTT (Con t x i) = Var $ UN (show x)
>        forgetTT (TyCon x i) = Var $ UN (show x)
>        forgetTT (Elim x) = Var $ UN (show x)
>        forgetTT (App f a) = RApp (forgetTT f) (forgetTT a)
>        forgetTT (Bind n (B Lambda t) (Sc sc)) =
>                    (RBind (UN (show n)) (B Lambda (forget t)) (forget sc))
>        forgetTT (Bind n (B Pi t) (Sc sc)) =
>                    (RBind (UN (show n)) (B Pi (forget t)) (forget sc))
>        forgetTT (Bind n (B (Let v) t) (Sc sc)) =
>                    (RBind (UN (show n)) (B (Let (forget v)) (forget t))
>				(forget sc))
>        forgetTT (Bind n (B Hole t) (Sc sc)) =
>                    (RBind (UN (show n)) (B Hole (forget t)) (forget sc))
>        forgetTT (Bind n (B (Guess v) t) (Sc sc)) =
>                    (RBind (UN (show n)) (B (Guess (forget v)) (forget t))
>				(forget sc))
>        forgetTT (Bind n (B (Pattern v) t) (Sc sc)) =
>                    (RBind (UN (show n)) (B (Pattern (forget v)) (forget t))
>				(forget sc))
>        forgetTT (Proj n i t) = RAnnot $ (show t)++"!"++(show i)++":"++show n
>        forgetTT (Label t (Comp n cs)) = RLabel (forgetTT t)
>                                          (RComp (UN $ show n)
>                                             (map forgetTT cs))
>        forgetTT (Call (Comp n cs) t) = RCall (RComp (UN $ show n)
>                                               (map forgetTT cs))
>                                                 (forgetTT t)
>        forgetTT (Return t) = RReturn (forgetTT t)
>        forgetTT (Stage (Quote t)) = RStage (RQuote (forgetTT t))
>        forgetTT (Stage (Code t)) = RStage (RCode (forgetTT t))
>        forgetTT (Stage (Eval t _)) = RStage (REval (forgetTT t))
>        forgetTT (Stage (Escape t _)) = RStage (REscape (forgetTT t))
>        forgetTT (Const x) = RConst x
>        forgetTT Star = RStar
