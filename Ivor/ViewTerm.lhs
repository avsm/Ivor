> {-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}

> -- | 
> -- Module      : Ivor.ViewTerm
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> -- 
> -- Exported view of terms and inductive data structures; imported 
> -- implicitly by "Ivor.TT".

> module Ivor.ViewTerm(-- * Variable names
>                        Name,name,displayName,NameType(..),mkVar,
>                        -- * Terms
>                        Term(..), ViewTerm(..), Annot(..), apply,
>                        view, viewType, ViewConst, typeof, 
>                        freeIn, namesIn, occursIn, subst, getApp, 
>                        Ivor.ViewTerm.getFnArgs,
>                        getArgTypes, Ivor.ViewTerm.getReturnType,
>                        dbgshow,
>                        -- * Inductive types
>                        Inductive(..)) 
>    where

> import Ivor.TTCore as TTCore hiding (subst)
> import Ivor.Gadgets
> import Ivor.State
> import Ivor.Typecheck

> import Data.Typeable
> import Data.List

> name :: String -> Name
> name = UN

> displayName :: Name -> String
> displayName (UN x) = x
> displayName (MN (x,i)) = "_" ++ x ++ "_" ++ show i

> -- | Abstract type representing a TT term and its type.
> newtype Term = Term (Indexed Name, Indexed Name)

> instance Show Term where
>     show (Term (Ind tm,Ind ty)) 
>         = show (makePs tm) ++ " : " ++ show (makePs ty) ++ "\n"

> -- | Categories for names; typechecked terms will know what each variable
> -- is for. 
> data NameType = Bound | Free | DataCon | TypeCon | ElimOp 
>               | Unknown -- ^ Use for sending to typechecker.
>   deriving Show

> -- | Construct a term representing a variable
> mkVar :: String -- ^ Variable name
>          -> ViewTerm
> mkVar nm = Name Unknown (name nm)

> data ViewTerm 
>     = Name { nametype :: NameType, var :: Name }
>     | App { fun :: ViewTerm, arg :: ViewTerm }
>     | Lambda { var :: Name, vartype :: ViewTerm, scope :: ViewTerm }
>     | Forall { var :: Name, vartype :: ViewTerm, scope :: ViewTerm }
>     | Let { var :: Name, vartype :: ViewTerm,
>             varval :: ViewTerm, scope :: ViewTerm }
>     | Label { fname :: Name, fargs :: [ViewTerm], labeltype :: ViewTerm }
>     | Call { fname :: Name, fargs :: [ViewTerm], callterm :: ViewTerm }
>     | Return { returnterm :: ViewTerm }
>     | forall c. Constant c => Constant c
>     | Star
>     | Quote { quotedterm :: ViewTerm } -- ^ Staging annotation
>     | Code { codetype :: ViewTerm } -- ^ Staging annotation
>     | Eval { evalterm :: ViewTerm } -- ^ Staging annotation
>     | Escape { escapedterm :: ViewTerm } -- ^ Staging annotation
>     | Placeholder
>     | Annotation { annotation :: Annot,
>                    term :: ViewTerm } -- ^ additional annotations
>     | Metavar { var :: Name }

> data Annot = FileLoc FilePath Int -- ^ source file, line number

> instance Eq ViewTerm where
>     (==) (Name _ x) (Name _ y) = x == y
>     (==) (Ivor.ViewTerm.App f a) (Ivor.ViewTerm.App f' a') = f == f' && a == a'
>     (==) (Ivor.ViewTerm.Lambda n ty sc) (Ivor.ViewTerm.Lambda n' ty' sc') = n==n' && ty==ty' && sc==sc'
>     (==) (Forall n ty sc) (Forall n' ty' sc') = n==n' && ty==ty' && sc==sc'
>     (==) (Ivor.ViewTerm.Let n v ty sc) (Ivor.ViewTerm.Let n' v' ty' sc') = n==n' && v==v' 
>                                                 && ty==ty' && sc==sc'
>     (==) (Ivor.ViewTerm.Label _ _ ty) (Ivor.ViewTerm.Label _ _ ty') = ty == ty'
>     (==) (Ivor.ViewTerm.Call _ _ t) (Ivor.ViewTerm.Call _ _ t') = t == t'
>     (==) (Ivor.ViewTerm.Return t) (Ivor.ViewTerm.Return t') = t==t'
>     (==) Ivor.ViewTerm.Star Ivor.ViewTerm.Star = True
>     (==) Placeholder Placeholder = True
>     (==) (Metavar x) (Metavar y) = x == y
>     (==) (Constant x) (Constant y) = case cast x of
>                                        Just x' -> x' == y
>                                        Nothing -> False
>     (==) (Ivor.ViewTerm.Quote t) (Ivor.ViewTerm.Quote t') = t==t'
>     (==) (Ivor.ViewTerm.Code t) (Ivor.ViewTerm.Code t') = t==t'
>     (==) (Ivor.ViewTerm.Eval t) (Ivor.ViewTerm.Eval t') = t==t'
>     (==) (Ivor.ViewTerm.Escape t) (Ivor.ViewTerm.Escape t') = t==t'
>     (==) (Annotation _ t) (Annotation _ t') = t == t'
>     (==) _ _ = False

> -- | Haskell types which can be used as constants
> class (Typeable c, Show c, Eq c) => ViewConst c where
>     typeof :: c -> Name

> instance ViewConst c => Constant c where
>     constType x = TyCon (typeof x) 0

> -- | Make an application of a function to several arguments
> apply :: ViewTerm -> [ViewTerm] -> ViewTerm
> apply f [] = f
> apply f (x:xs) = Ivor.ViewTerm.apply (Ivor.ViewTerm.App f x) xs

> data Inductive
>     = Inductive { typecon :: Name, 
>                   parameters :: [(Name,ViewTerm)],
>                   indices :: [(Name,ViewTerm)],
>                   contype :: ViewTerm,
>                   constructors :: [(Name,ViewTerm)] }

> instance Forget ViewTerm Raw where
>     forget (Ivor.ViewTerm.App f a) = RApp (forget f) (forget a)
>     forget (Ivor.ViewTerm.Lambda v ty sc) = RBind v 
>                                            (B TTCore.Lambda (forget ty)) 
>                                            (forget sc)
>     forget (Forall v ty sc) = RBind v (B Pi (forget ty)) (forget sc)
>     forget (Ivor.ViewTerm.Let v ty val sc) = RBind v (B (TTCore.Let (forget val))
>                                                  (forget ty)) (forget sc)
>     forget (Ivor.ViewTerm.Label n args ty) 
>         = RLabel (forget ty) (RComp n (map forget args))
>     forget (Ivor.ViewTerm.Call n args ty) 
>         = RCall (RComp n (map forget args)) (forget ty)
>     forget (Ivor.ViewTerm.Return ty) = RReturn (forget ty)
>     forget (Constant c) = RConst c
>     forget (Ivor.ViewTerm.Star) = TTCore.RStar
>     forget Placeholder = RInfer
>     forget (Metavar x) = RMeta x
>     forget (Ivor.ViewTerm.Quote t) = RStage (RQuote (forget t))
>     forget (Ivor.ViewTerm.Code t) = RStage (RCode (forget t))
>     forget (Ivor.ViewTerm.Eval t) = RStage (REval (forget t))
>     forget (Ivor.ViewTerm.Escape t) = RStage (REscape (forget t))
>     forget (Annotation (FileLoc f l) t) = RFileLoc f l (forget t)
>     forget x = Var (var x)

> instance Show ViewTerm where
>     show = show.forget

> instance Forget Inductive String where
>     forget (Inductive n ps inds cty cons) =
>         show n++" "++showbind ps++" : "++showbind inds++show (forget cty)
>                  ++ " = "++
>                showcons cons
>       where showbind [] = ""
>             showbind ((x,ty):xs) = "("++show x++":"++show (forget ty)++")"
>                                    ++ showbind xs
>             showcons [] = ""
>             showcons [x] = showcon x
>             showcons (x:xs) = showcon x ++ " | " ++ showcons xs
>             showcon (x,ty) = show x ++ " : " ++ show (forget ty)

> instance Show Inductive where
>     show = forget

> -- |Get a pattern matchable representation of a term.
> view :: Term -> ViewTerm
> view (Term (Ind tm,_)) = vt (Ind (makePs tm))

> -- |Get a pattern matchable representation of a term's type.
> viewType :: Term -> ViewTerm
> viewType (Term (_,Ind ty)) = vt (Ind (makePs ty))

> vt :: Indexed Name -> ViewTerm
> vt (Ind tm) = vtaux [] tm where
>     vtaux ctxt (P n) = Name Free n
>     vtaux ctxt (V i) = Name Bound (traceIndex ctxt i "ViewTerm vt")
>     vtaux ctxt (Con _ n _) = Name DataCon n
>     vtaux ctxt (TyCon n _) = Name TypeCon n
>     vtaux ctxt (Elim n) = Name ElimOp n
>     vtaux ctxt (TTCore.App f a) = Ivor.ViewTerm.App (vtaux ctxt f) (vtaux ctxt a)
>     vtaux ctxt (Bind n (B TTCore.Lambda ty) (Sc sc)) =
>         Ivor.ViewTerm.Lambda n (vtaux ctxt ty) (vtaux (n:ctxt) sc)
>     vtaux ctxt (Bind n (B Pi ty) (Sc sc)) =
>         Forall n (vtaux ctxt ty) (vtaux (n:ctxt) sc)
>     vtaux ctxt (Bind n (B (TTCore.Let val) ty) (Sc sc)) =
>         Ivor.ViewTerm.Let n (vtaux ctxt ty) (vtaux ctxt val) (vtaux (n:ctxt) sc)
>     vtaux ctxt (Const c) = Constant c
>     vtaux ctxt TTCore.Star = Ivor.ViewTerm.Star
>     vtaux ctxt (TTCore.Label ty (Comp n ts)) =
>         Ivor.ViewTerm.Label n (fmap (vtaux ctxt) ts) (vtaux ctxt ty)
>     vtaux ctxt (TTCore.Call (Comp n ts) ty) =
>         Ivor.ViewTerm.Call n (fmap (vtaux ctxt) ts) (vtaux ctxt ty)
>     vtaux ctxt (TTCore.Return ty) = Ivor.ViewTerm.Return (vtaux ctxt ty)
>     vtaux ctxt (Stage (TTCore.Quote tm)) 
>         = Ivor.ViewTerm.Quote (vtaux ctxt tm)
>     vtaux ctxt (Stage (TTCore.Code tm)) 
>         = Ivor.ViewTerm.Code (vtaux ctxt tm)
>     vtaux ctxt (Stage (TTCore.Eval tm _)) 
>         = Ivor.ViewTerm.Eval (vtaux ctxt tm)
>     vtaux ctxt (Stage (TTCore.Escape tm _)) 
>         = Ivor.ViewTerm.Escape (vtaux ctxt tm)
>     vtaux _ t = error $ "Can't happen vtaux " ++ debugTT t

> -- | Return whether the name occurs free in the term.
> freeIn :: Name -> ViewTerm -> Bool
> freeIn n t = fi n t where
>    fi n (Ivor.ViewTerm.Name _ x) | x == n = True
>                    | otherwise = False
>    fi n (Ivor.ViewTerm.App f a) = fi n f || fi n a
>    fi n (Ivor.ViewTerm.Lambda x ty sc) 
>        | x == n = False
>        | otherwise = fi n ty || fi n sc
>    fi n (Forall x ty sc) | x == n = False
>                          | otherwise = fi n ty || fi n sc
>    fi n (Ivor.ViewTerm.Let x v ty sc) 
>        | x == n = False
>        | otherwise = fi n v || fi n ty || fi n sc
>    fi n (Ivor.ViewTerm.Label _ _ t) = fi n t
>    fi n (Ivor.ViewTerm.Call _ _ t) = fi n t
>    fi n (Ivor.ViewTerm.Return t) = fi n t
>    fi n (Ivor.ViewTerm.Quote t) = fi n t
>    fi n (Ivor.ViewTerm.Code t) = fi n t
>    fi n (Ivor.ViewTerm.Eval t) = fi n t
>    fi n (Ivor.ViewTerm.Escape t) = fi n t
>    fi n (Annotation _ t) = fi n t
>    fi n _ = False

> -- | Return the names occurring free in a term
> namesIn :: ViewTerm -> [Name]
> namesIn t = nub $ fi [] t where
>    fi ns (Ivor.ViewTerm.Name _ x) | x `elem` ns = []
>                                   | otherwise = [x]
>    fi ns (Ivor.ViewTerm.App f a) = fi ns f ++ fi ns a
>    fi ns (Ivor.ViewTerm.Lambda x ty sc) = fi (x:ns) sc
>    fi ns (Forall x ty sc) = fi (x:ns) sc
>    fi ns (Ivor.ViewTerm.Let x v ty sc) = fi (x:ns) sc
>    fi ns (Ivor.ViewTerm.Label _ _ t) = fi ns t
>    fi ns (Ivor.ViewTerm.Call _ _ t) = fi ns t
>    fi ns (Ivor.ViewTerm.Return t) = fi ns t
>    fi ns (Ivor.ViewTerm.Quote t) = fi ns t
>    fi ns (Ivor.ViewTerm.Code t) = fi ns t
>    fi ns (Ivor.ViewTerm.Eval t) = fi ns t
>    fi ns (Ivor.ViewTerm.Escape t) = fi ns t
>    fi ns (Annotation _ t) = fi ns t
>    fi ns _ = []

> -- | Return whether a subterm occurs in a (first order) term.
> occursIn :: ViewTerm -> ViewTerm -> Bool
> occursIn n t = fi n t where
>    fi n (Ivor.ViewTerm.App f a) = fi n f || fi n a
>    fi n (Ivor.ViewTerm.Lambda x ty sc) = False -- higher order
>    fi n (Forall x ty sc) = False
>    fi n (Ivor.ViewTerm.Let x v ty sc)  = False
>    fi n (Ivor.ViewTerm.Label _ _ t) = fi n t
>    fi n (Ivor.ViewTerm.Call _ _ t) = fi n t
>    fi n (Ivor.ViewTerm.Return t) = fi n t
>    fi n (Ivor.ViewTerm.Code t) = fi n t
>    fi n (Ivor.ViewTerm.Eval t) = fi n t
>    fi n (Ivor.ViewTerm.Escape t) = fi n t
>    fi n (Annotation _ t) = fi n t
>    fi n x = n == x

> -- | Get the function from an application. If no application, returns the
> -- entire term.
> getApp :: ViewTerm -> ViewTerm
> getApp (Ivor.ViewTerm.App f a) = getApp f
> getApp (Annotation _ t) = getApp t
> getApp x = x

> -- | Get the arguments from a function application.
> getFnArgs :: ViewTerm -> [ViewTerm]
> getFnArgs (Ivor.ViewTerm.App f a) = Ivor.ViewTerm.getFnArgs f ++ [a]
> getFnArgs (Annotation _ t) = getFnArgs t
> getFnArgs x = []

> -- | Get the argument names and types from a function type
> getArgTypes :: ViewTerm -> [(Name, ViewTerm)]
> getArgTypes (Ivor.ViewTerm.Forall n ty sc) = (n,ty):(getArgTypes sc)
> getArgTypes (Annotation _ t) = getArgTypes t
> getArgTypes x = []

> -- | Get the return type from a function type
> getReturnType :: ViewTerm -> ViewTerm
> getReturnType (Ivor.ViewTerm.Forall n ty sc) = Ivor.ViewTerm.getReturnType sc
> getReturnType (Annotation _ t) = Ivor.ViewTerm.getReturnType t
> getReturnType x = x

> dbgshow (UN n) = "UN " ++ show n
> dbgshow (MN (n,i)) = "MN [" ++ show n ++ "," ++ show i ++ "]"

> -- | Match the second argument against the first, returning a list of
> -- the names in the first paired with their matches in the second. Returns
> -- Nothing if there is a match failure. There is no searching under binders.
> match :: ViewTerm -> ViewTerm -> Maybe [(Name, ViewTerm)]
> match t1 t2 = do acc <- m' t1 t2 []
>                  checkDups acc [] where
>   m' (Name _ n) t acc = return ((n,t):acc)
>   m' (Ivor.ViewTerm.App f a) (Ivor.ViewTerm.App f' a') acc 
>       = do acc' <- m' f f' acc
>            m' a a' acc'
>   m' (Annotation _ t) t' acc = m' t t' acc
>   m' t (Annotation _ t') acc = m' t t' acc
>   m' x y acc | x == y = return acc
>              | otherwise = fail $"Mismatch " ++ show x ++ " and " ++ show y

>   checkDups [] acc = return acc
>   checkDups ((x,t):xs) acc 
>      = case lookup x xs of
>          Just t' -> if t == t' then checkDups xs acc
>                                else fail $ "Mismatch on " ++ show x
>          Nothing -> checkDups xs ((x,t):acc)

> -- |Substitute a name n with a value v in a term f 
> subst :: Name -> ViewTerm -> ViewTerm -> ViewTerm
> subst n v nm@(Name _ p) | p == n = v
>                         | otherwise = nm
> subst n v (Ivor.ViewTerm.App f a) 
>    = Ivor.ViewTerm.App (subst n v f) (subst n v a)
> subst n v (Ivor.ViewTerm.Lambda nn ty sc) 
>    = Ivor.ViewTerm.Lambda nn (subst n v ty) $
>         if (n==nn) then sc else subst n v sc
> subst n v (Forall nn ty sc) 
>    = Forall nn (subst n v ty) $
>         if (n==nn) then sc else subst n v sc
> subst n v (Ivor.ViewTerm.Let nn ty vv sc) 
>    = Ivor.ViewTerm.Let nn (subst n v ty) (subst n v vv) $
>         if (n==nn) then sc else subst n v sc
> subst n v (Ivor.ViewTerm.Label fn args ty)
>    = Ivor.ViewTerm.Label fn (map (subst n v) args) (subst n v ty)
> subst n v (Ivor.ViewTerm.Call fn args ty)
>    = Ivor.ViewTerm.Call fn (map (subst n v) args) (subst n v ty)
> subst n v (Ivor.ViewTerm.Return r) 
>           = Ivor.ViewTerm.Return (subst n v r)
> subst n v (Ivor.ViewTerm.Quote r) 
>           = Ivor.ViewTerm.Quote (subst n v r)
> subst n v (Ivor.ViewTerm.Code r) 
>           = Ivor.ViewTerm.Code (subst n v r)
> subst n v (Ivor.ViewTerm.Eval r) 
>           = Ivor.ViewTerm.Eval (subst n v r)
> subst n v (Ivor.ViewTerm.Escape r) 
>           = Ivor.ViewTerm.Escape (subst n v r)
> subst n v (Annotation a t) = Annotation a (subst n v t)
> subst n v t = t

