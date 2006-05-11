> {-# OPTIONS_GHC -fglasgow-exts #-}

> module TT where

> import Gadgets
> import List
> import Char
> import Control.Monad.State

Raw terms are those read in directly from the user, and may be badly typed.
(Maybe add labels later)

> data Raw 
>     = Var Name
>     | RApp Raw Raw
>     | RBind Name (Binder Raw) Raw
>     | RConst Const
>     | RAnnot String -- Debugging hack
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
>     | Proj Int (TT n) -- Projection in iota schemes
>     | Const Const

Constants

> data Const = Star
>     deriving (Eq)

> instance Show Const where
>     show Star = "*"

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
>    deriving (Show, Eq)

Local environments

> type Env n = [(n,Binder (TT n))]

Separate types for de Bruijn indexed terms and de Bruijn levelled terms

> newtype Levelled n = Lev (TT n) deriving Eq
> newtype Indexed n = Ind (TT n) deriving Eq

Pattern represents the patterns used to define iota schemes.

> data Pattern n =
>	 PVar n  -- Variable
>      | PCon Int n [Pattern n] -- Constructor, with tag
>      | PMarkCon n [Pattern n] -- Detagged constructor
>      | PTerm -- Presupposed term (don't care what it is)
>      | PMark n  -- Marked variable
>      | PConst Const -- Constant
>  deriving (Show, Eq)

> instance Eq n => Ord (Pattern n) where
>     compare (PCon x _ _) (PCon y _ _) = compare x y
>     compare _ _ = EQ -- Don't care!

UN covers names defined by users, MN covers names invented by the system.
This keeps both namespaces separate.

> data Name 
>     = UN String
>     | MN (String,Int) 
>   deriving Eq

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

> instance Functor TT where
>     fmap f (P x) = P (f x)
>     fmap f (V i) = V i
>     fmap f (Con t x i) = Con t (f x) i
>     fmap f (TyCon x i) = TyCon (f x) i
>     fmap f (Elim x) = Elim (f x)
>     fmap f (App tf a) = App (fmap f tf) (fmap f a)
>     fmap f (Bind n b sc) = Bind (f n) (fmap (fmap f) b) (fmap (fmap f) sc)
>     fmap f (Proj i x) = Proj i (fmap f x)
>     fmap f (Const x) = Const x

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
>     v' ctx (Proj i x) = Proj i (v' ctx x)
>     v' ctx x = x

> indexise :: Levelled n -> Indexed n
> indexise (Lev t) = Ind $ vapp (\ (ctx,i) -> V (i-((length ctx)-1))) t

> levelise :: Indexed n -> Levelled n
> levelise (Ind t) = Lev $ vapp (\ (ctx,i) -> V ((length ctx)-i-1)) t

FIXME: This needs to rename all duplicated binder names first, otherwise
we get a duff term when we go back to the indexed version.

> makePs :: TT Name -> TT Name
> makePs t = let t' = evalState (uniqifyAllState t) [] in
>                 vapp (\ (ctx,i) -> P (ctx!!i)) t'

> makePsEnv env t = let t' = evalState (uniqifyAllState t) env in
>                       vapp (\ (ctx,i) -> P (ctx!!i)) t'


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
> uniqifyAllState (Proj i t) = 
>     do t' <- uniqifyAllState t
>        return (Proj i t')
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

Check the purity of a term; a term is pure iff it has no holes.

> pure :: TT Name -> Bool
> pure (Bind _ (B b ty) (Sc sc)) = purebind b && pure ty && pure sc
> pure (App f a) = pure f && pure a
> pure (Proj _ t) = pure t
> pure _ = True
>
> purebind Hole = False -- Seems a bit OTT to use a type class just for this...
> purebind (Guess _) = False
> purebind (Let t) = pure t
> purebind _ = True

Substitute a term into V 0 in the scope (and weaken other indices)
This'll never work. de Bruijn index mangling breaks my brain.

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
>     p' (Proj i x) = p' x
>     p' x = []
>     pb' (B (Let v) ty) = p' v ++ p' ty
>     pb' (B (Guess v) ty) = p' v ++ p' ty
>     pb' (B _ ty) = p' ty

The following gadgets expect a fully explicitly named term, rather than
with de Bruijn indices or levels. We need a newtype Named n.

> substName :: Eq n => n -> TT n -> Scope (TT n) -> TT n
> substName p tm (Sc x) = p' x where
>     p' (P x) | x == p = tm
>     p' (App f' a) = (App (p' f') (p' a))
>     p' (Bind n b (Sc sc)) = (Bind n (fmap p' b) (Sc (p' sc)))
>      --   | n == p = (Bind n (fmap p' b) (Sc sc))
>      --   | otherwise 
>     p' (Proj i x) = Proj i (p' x)
>     p' x = x

Look for a specific term and replace it.
Probably hopelessly inefficient.

> substTerm :: Eq n => TT n -> TT n -> Scope (TT n) -> TT n
> substTerm p tm (Sc x) = p' x where
>     p' x | x == p = tm
>     p' (App f' a) = (App (p' f') (p' a))
>     p' (Bind n b (Sc sc)) = (Bind n (fmap p' b) (Sc (p' sc)))
>      --   | n == p = (Bind n (fmap p' b) (Sc sc))
>      --   | otherwise 
>     p' (Proj i x) = Proj i (p' x)
>     p' x = x

> getSc (Sc x) = x

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
>    where incName x | (num,name) <- span isDigit (reverse x)
>                        = (reverse name)++show (inc num)
>
>          inc "" = 0
>          inc xs = (read (reverse xs)) + 1

Bind a list of things

> bind :: Bind (TT Name) -> [(Name,TT Name)] -> Scope (TT Name) -> TT Name
> bind binder [] sc = getSc sc
> bind binder ((n,ty):xs) sc = Bind n (B binder ty) (Sc (bind binder xs sc))

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

> instance Eq n => Eq (TT n) where
>     (==) (P x) (P y) = x==y
>     (==) (V i) (V j) = i==j
>     (==) (Con t x i) (Con t' y j) = x==y
>     (==) (TyCon x i) (TyCon y j) = x==y
>     (==) (Elim x) (Elim y) = x==y
>     (==) (App f a) (App f' a') = f==f' && a==a'
>     (==) (Bind _ b sc) (Bind _ b' sc') = b==b' && sc==sc'
>     (==) (Proj i x) (Proj j y) = i==j && x==y
>     (==) (Const x) (Const y) = x==y
>     (==) _ _ = False

===================== Forgetful maps ==============================

> instance Forget Name String where
>     forget (UN n) = n
>     forget (MN (x,i)) = x ++ "[" ++ show i ++ "]"

> instance Forget Raw String where
>     forget (Var n) = forget n
>     forget (RApp f a) = "(" ++ forget f ++ " " ++ forget a ++ ")"
>     forget (RBind n (B Lambda t) sc) = "["++forget n ++":"++forget t++"]" 
>				 ++ forget sc
>     forget (RBind n (B Pi t) sc) = "("++forget n ++":"++forget t++")" 
>				 ++ forget sc
>     forget (RBind n (B (Let v) t) sc) = "let "++forget n ++":"++forget t
>                                 ++"=" ++ forget v ++ " in " ++ forget sc
>     forget (RBind n (B Hole t) sc) = "?"++forget n ++":"++forget t++"." 
>				 ++ forget sc
>     forget (RBind n (B (Guess v) t) sc) = "try "++forget n ++":"++forget t
>                                 ++"=" ++ forget v ++ " in " ++ forget sc
>     forget (RConst Star) = "*"
>     forget (RAnnot t) = t

> instance Show n => Forget (Indexed n) Raw where
>     forget (Ind t) = forget t

> instance Show n => Forget (Levelled n) Raw where
>     forget (Lev t) = forget t

> instance Show n => Forget (TT n) Raw where
>     forget t = forgetTT (vapp showV t)
>      where
>        showV (ctx,i) | i < length ctx = P (ctx!!i)
>	               | otherwise = V i
>	 forgetTT (P x) = Var $ UN (show x)
>        forgetTT (V i) = RAnnot $ "v" ++ (show i)
>        forgetTT (Con t x i) = Var $ UN (show x)
>        forgetTT (TyCon x i) = Var $ UN (show x)
>	 forgetTT (Elim x) = Var $ UN (show x)
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
>        forgetTT (Proj i t) = RAnnot $ (show t)++"!"++(show i)
>        forgetTT (Const x) = RConst x


> testid = (Bind (UN "x") (B Lambda (Const Star)) (Sc (V 0)))
> testterm = (App testid (Const Star))

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

