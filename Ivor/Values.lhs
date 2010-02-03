> {-# OPTIONS_GHC -fglasgow-exts #-}

FIXME: Most of this stuff and Ivor.Nobby have GOT TO GO!!!

> module Ivor.Values where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Constant

> import Debug.Trace
> import Data.Typeable
> import Control.Monad.State
> import List
> import qualified Data.Map as Map

To begin, we need to define the context in which normalisation takes place.
The context maps names to user defined functions, constructors and
elimination rules.

Global represents all possible global names --- if it's a user defined
name, hold its definition, otherwise hold what it is so we know what
to do with it, when the time comes.

> data Global n
>     = Fun [FunOptions] (Indexed n)    -- User defined function
>     | Partial (Indexed n) [n] -- Unfinished definition
>     | PatternDef (PMFun n) Bool Bool -- Pattern matching definition, totality, generated
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

> defplicit :: Int
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
>     | BMeta Name (Model s)
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
