> {-# OPTIONS_GHC -fglasgow-exts #-}

> -- | 
> -- Module      : Ivor.TT
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> -- 
> -- Public interface for theorem proving gadgets.

> module Ivor.TT(-- * System state
>               emptyContext, Context,
>               Ivor.TT.check,
>               checkCtxt,converts,
>               Ivor.TT.compile,
>               -- * Exported view of terms
>               module VTerm, IsTerm, IsData,
>               -- * Definitions and Theorems
>               addDef,addTypedDef,addData,addAxiom,declare,declareData,
>               theorem,interactive,
>               addPrimitive,addBinOp,addBinFn,addPrimFn,addExternalFn,
>               addEquality,forgetDef,addGenRec,addImplicit,
>               -- * Pattern matching definitions
>               PClause(..), Patterns(..),PattOpt(..),addPatternDef,
>               -- * Manipulating Proof State
>               proving,numUnsolved,suspend,resume,
>               save, restore, clearSaved,
>               proofterm, getGoals, getGoal, uniqueName, -- getActions
>               allSolved,qed,
>               -- * Examining the Context
>               eval, whnf, evalCtxt, getDef, defined, getPatternDef, 
>               getAllDefs, getConstructors,
>               Rule(..), getElimRule,
>               Ivor.TT.freeze,Ivor.TT.thaw,
>               -- * Goals, tactic types
>               Goal,goal,defaultGoal,
>               Tactic, --Tactics.TacticAction(..),
>               GoalData, bindings, goalName, goalType,
>               goalData, subGoals,
>               -- * Primitive Tactics
>               -- ** Basics
>               intro,
>               introName,
>               intros,intros1,
>               introsNames,
>               Ivor.TT.addArg,
>               generalise,
>               dependentGeneralise,
>               claim,
>               -- ** Proof navigation
>               focus,
>               rename,
>               attack, attackWith,
>               solve,
>               trySolve,
>               keepSolving,
>               abandon,
>               hide,
>               -- ** Introductions
>               fill,
>               refine,
>               basicRefine,
>               refineWith,
>               trivial,
>               axiomatise,
>               -- ** Eliminations
>               by,
>               induction,
>               cases,
>               -- ** Conversions
>               equiv,
>               compute,
>               beta,
>               unfold,
>               -- ** Equality
>               replace,
>               -- ** Computations
>               call,
>               returnComputation,
>               -- ** Staging
>               quoteVal,
>               -- ** Tactic combinators
>               idTac, tacs,
>               (>->), (>=>), (>+>), (>|>), try, 
>               traceTac)

>     where

> import Ivor.TTCore as TTCore
> import Ivor.State
> import Ivor.Typecheck
> import Ivor.Gadgets
> import Ivor.Nobby
> import Ivor.Evaluator
> import Ivor.SC
> import Ivor.Bytecode
> import Ivor.Datatype
> import Ivor.Constant
> import Ivor.ViewTerm as VTerm
> import Ivor.TermParser
> import qualified Ivor.Tactics as Tactics
> import Ivor.Compiler as Compiler
> import Ivor.CodegenC
> import Ivor.PatternDefs

> import List
> import Debug.Trace
> import Data.Typeable

> -- | Abstract type representing state of the system.
> newtype Context = Ctxt IState

> -- | Abstract type representing goal or subgoal names.
> data Goal = Goal Name | DefaultGoal
>     deriving Eq

> instance Show Goal where
>     show (Goal g) = show g
>     show (DefaultGoal) = "Default Goal"

> goal :: String -> Goal
> goal g = Goal $ UN g

> defaultGoal :: Goal
> defaultGoal = DefaultGoal

> -- |A tactic is any function which manipulates a term at the given goal 
> -- binding. Tactics may fail, hence the monad.
> type Tactic = forall m.Monad m => Goal -> Context -> m Context

> -- | Initialise a context, with no data or definitions and an 
> -- empty proof state.
> emptyContext :: Context
> emptyContext = Ctxt initstate

> class IsTerm a where
>     -- | Typecheck a term
>     check :: Monad m => Context -> a -> m Term
>     raw :: Monad m => a -> m Raw

> class IsData a where
>     addData :: Monad m => Context -> a -> m Context

> instance IsTerm Term where
>     check _ tm = return tm
>     raw tm = return $ forget (view tm)

> instance IsTerm ViewTerm where
>     check ctxt tm = Ivor.TT.check ctxt (forget tm)
>     raw tm = return $ forget tm

> instance IsTerm String where
>     check ctxt str = case parseTermString str of
>          (Success tm) -> Ivor.TT.check ctxt (forget tm)
>          (Failure err) -> fail err
>     raw str = case parseTermString str of
>          (Success tm) -> return $ forget tm
>          (Failure err) -> fail err

> instance IsTerm Raw where
>     check (Ctxt st) t = do
>        case (typecheck (defs st) t) of
>           (Success (t, ty)) -> return $ Term (t,ty)
>           (Failure err) -> fail err
>     raw t = return t

> -- | Parse and typecheck a data declaration, of the form
> -- "x:Type = c1:Type | ... | cn:Type"
> instance IsData String where
>     addData (Ctxt st) str = do
>         case (parseDataString str) of
>             Success ind -> addData (Ctxt st) ind
>             Failure err -> fail err

> instance IsData Inductive where
>     addData (Ctxt st) ind = do st' <- doMkData st (datadecl ind)
>                                return (Ctxt st')
>       where
>         datadecl (Inductive n ps inds cty cons) = 
>             Datadecl n (map (\ (n,ty) -> (n, forget ty)) ps)
>                        (mkTycon inds cty)
>                        (map (\ (n,ty) -> (n, forget ty)) cons)
>         mkTycon [] rty = forget rty
>         mkTycon ((n,ty):ts) rty = RBind n (B Pi (forget ty)) (mkTycon ts rty)

> checkNotExists n gam = case lookupval n gam of
>                                 Just Undefined -> return ()
>                                 Just (TCon _ NoConstructorsYet) -> return ()
>                                 Just _ -> fail $ show n ++ " already defined"
>                                 Nothing -> return ()

> data PClause = PClause {
>                         arguments :: [ViewTerm],
>                         returnval :: ViewTerm
>                        }
>    deriving Show

> data Patterns = Patterns [PClause]
>    deriving Show

> mkRawClause :: PClause -> RawScheme
> mkRawClause (PClause args ret) =
>     RSch (map forget args) (forget ret)

> data PattOpt = Partial -- ^ No need to cover all cases
>              | GenRec -- ^ No termination checking
>   deriving Eq

> -- |Add a new definition to the global state.
> -- By default, these definitions must cover all cases and be well-founded,
> -- but can be optionally partial or general recursive
> addPatternDef :: (IsTerm ty, Monad m) => 
>                Context -> Name -> ty -- ^ Type
>                  -> Patterns -- ^ Definition
>                -> [PattOpt] -- ^ Options to set which definitions will be accepted
>                -> m Context
> addPatternDef (Ctxt st) n ty pats opts = do
>         checkNotExists n (defs st)
>         inty <- raw ty
>         let (Patterns clauses) = pats
>         (pmdef, fty) <- checkDef (defs st) n inty (map mkRawClause clauses)
>                            (not (elem Ivor.TT.Partial opts))
>                            (not (elem GenRec opts))
>         newdefs <- gInsert n (G (PatternDef pmdef) fty defplicit) (defs st)
>         return $ Ctxt st { defs = newdefs }

> -- |Add a new definition, with its type to the global state.
> -- These definitions can be recursive, so use with care.
> addTypedDef :: (IsTerm term, IsTerm ty, Monad m) => 
>                Context -> Name -> term -> ty -> m Context
> addTypedDef (Ctxt st) n tm ty = do
>         checkNotExists n (defs st)
>         (Term (inty,_)) <- Ivor.TT.check (Ctxt st) ty
>         (Ctxt tmpctxt) <- declare (Ctxt st) n ty
>         let Gam tmp = defs tmpctxt
>         let Gam ctxt = defs st
>         let runtts = runtt st
>         term <- raw tm
>         case (checkAndBind (Gam tmp) [] term (Just inty)) of
>              (Success (v,t,_)) -> do
>                 if (convert (defs st) inty t)
>                     then (do
>                       newdefs <- gInsert n (G (Fun [Recursive] v) t defplicit) (Gam ctxt)
>                               -- = Gam ((n,G (Fun [] v) t):ctxt)
>                       let scs = lift n (levelise (normalise (Gam []) v))
>                       let bc = compileAll (runtts++scs) scs
>                       let newbc = bc++(bcdefs st)
>                       return $ Ctxt st { defs = newdefs, bcdefs = newbc,
>                                    runtt = (runtts++scs) })
>                     else (fail $ "The given type and inferred type do not match, inferred " ++ show t)
>              (Failure err) -> fail err


> -- |Add a new definition to the global state.
> addDef :: (IsTerm a, Monad m) => Context -> Name -> a -> m Context
> addDef (Ctxt st) n tm = do
>         checkNotExists n (defs st)
>         v <- raw tm
>         let Gam ctxt = defs st
>         let runtts = runtt st
>         case (typecheck (Gam ctxt) v) of
>             (Success (v,t)) -> do
>                 newdefs <- gInsert n (G (Fun [] v) t defplicit) (Gam ctxt)
>                 -- let newdefs = Gam ((n,G (Fun [] v) t):ctxt)
>                 let scs = lift n (levelise (normalise (Gam []) v))
>                 let bc = compileAll (runtts++scs) scs
>                 let newbc = bc++(bcdefs st)
>                 return $ Ctxt st { defs = newdefs, bcdefs = newbc,
>                                    runtt = (runtts++scs) }
>             (Failure err) -> fail err

> -- |Forget a definition and all following definitions.
> forgetDef :: Monad m => Context -> Name -> m Context
> forgetDef (Ctxt st) n = do let (Gam olddefs) = defs st
>                            newdefs <- f olddefs n
>                            return $ Ctxt st { defs = Gam newdefs }
>   where f [] n = fail "No such name"
>         f (def@(x,_):xs) n | x == n = return xs
>                            | otherwise = f xs n

> -- |Add the general recursion elimination rule, thus making all further
> -- definitions untrustworthy :).
> addGenRec :: Monad m => Context -> Name -- ^ Name to give recursion rule
>                      -> m Context
> addGenRec (Ctxt st) n
>     = do checkNotExists n (defs st)
>          (Ctxt tmpctxt) <- addAxiom (Ctxt st) n
>                              "(P:*)(meth_general:(p:P)P)P"
>          let Gam tmp = defs tmpctxt
>          let Gam ctxt = defs st
>          let runtts = runtt st
>          general <- raw $ "[P:*][meth_general:(p:P)P](meth_general (" ++ 
>                            show n ++ " P meth_general))"
>          case (typecheck (Gam tmp) general) of
>              (Success (v,t)) -> do
>                 -- let newdefs = Gam ((n,G (Fun [] v) t):ctxt)
>                 newdefs <- gInsert n (G (Fun [] v) t defplicit) (Gam ctxt)
>                 let scs = lift n (levelise (normalise (Gam []) v))
>                 let bc = compileAll (runtts++scs) scs
>                 let newbc = bc++(bcdefs st)
>                 return $ Ctxt st { defs = newdefs, bcdefs = newbc,
>                                    runtt = (runtts++scs) }
>              (Failure err) -> fail $ "Can't happen (general): "++err

> -- | Add the heterogenous (\"John Major\") equality rule and its reduction
> addEquality :: Monad m => Context -> Name -- ^ Name to give equality type
>             -> Name -- ^ Name to give constructor
>             -> m Context
> addEquality ctxt@(Ctxt st) ty con = do
>     checkNotExists ty (defs st)
>     checkNotExists con (defs st)
>     rtycon <- eqTyCon ty
>     rdatacon <- eqCon (show ty) con
>     rerule <- eqElimType (show ty) (show con) "Elim"
>     rcrule <- eqElimType (show ty) (show con) "Case"
>     rischeme <- eqElimSch (show con)
>     let rdata = (RData rtycon [rdatacon] 2 rerule rcrule [rischeme] [rischeme])
>     st <- doData st ty rdata
>     return $ Ctxt st

> -- eqElim : (A:*)(a:A)(b:A)(q:JMEq A A a a)
> --       (Phi:(a':A)(target:JMEq A A a a')*)
> --       (meth_refl:(a:A)(Phi a (refl A a)))(Phi a q);
> -- eqelim A a Phi meth_refl a (refl A a) => meth_refl a 

> eqTyCon jmeq = do ty <- raw $ "(A:*)(B:*)(a:A)(b:B)*"
>                   return (jmeq, ty)

> eqCon jmeq refl = do ty <- raw $ "(A:*)(a:A)" ++ jmeq ++ " A A a a"
>                      return (refl, ty)

> eqElimType jmeq refl nm
>     = do ty <- raw $ 
>                 "(A:*)(a:A)(b:A)(q:" ++ jmeq ++ 
>                 " A A a b)(Phi:(a':A)(target:" ++
>                 jmeq ++ " A A a a')*)(meth_" ++
>                 refl ++ ":Phi a (" ++ refl ++ " A a))(Phi b q)"
>          return (name (jmeq++nm), ty)

> eqElimSch refl = do aty <- raw "A"
>                     a <- raw "a"
>                     b <- raw "_"
>                     phi <- raw "phi"
>                     mrefl <- raw "meth_refl"
>                     arg <- raw $ refl ++ " A a"
>                     ret <- raw "meth_refl"
>                     return $ RSch [aty,a,b,arg,phi,mrefl] ret

> -- | Declare a name which is to be defined later
> declare :: (IsTerm a, Monad m) => Context -> Name -> a -> m Context
> declare ctxt n tm = addUn Undefined ctxt n tm

> -- | Declare a type constructor which is to be defined later
> declareData :: (IsTerm a, Monad m) => Context -> Name -> a -> m Context
> declareData ctxt@(Ctxt st) n tm = do
>   let gamma = defs st
>   Term (ty, _) <- Ivor.TT.check ctxt tm
>   addUn (TCon (arity gamma ty) NoConstructorsYet) ctxt n tm

> -- | Add a new axiom to the global state.
> addAxiom :: (IsTerm a, Monad m) => Context -> Name -> a -> m Context
> addAxiom ctxt n tm = addUn Unreducible ctxt n tm

> addUn und (Ctxt st) n tm = do
>        checkNotExists n (defs st)
>        t <- raw tm
>        let Gam ctxt = defs st
>        case (typecheck (defs st) t) of
>           (Success (t, ty)) ->
>              do checkConv (defs st) ty (Ind TTCore.Star) "Not a type"
>                 -- let newdefs = Gam ((n, (G und (finalise t))):ctxt)
>                 newdefs <- gInsert n (G und (finalise t) defplicit) (Gam ctxt)
>                 return $ Ctxt st { defs = newdefs }
>           (Failure err) -> fail err

> -- | Add a new primitive type. This should be done in assocation with
> -- creating an instance of 'ViewConst' for the type, and creating appropriate
> -- primitive functions.
> addPrimitive :: Monad m => Context -> Name -- ^ Type name
>                 -> m Context
> addPrimitive (Ctxt st) n = do
>        checkNotExists n (defs st)
>        let Gam ctxt = defs st
>        let elims = Elims (MN ("none",0)) (MN ("none",0)) []
>        -- let newdefs = Gam ((n, (G (TCon 0 elims) (Ind TTCore.Star))):ctxt)
>        newdefs <- gInsert n (G (TCon 0 elims) (Ind TTCore.Star) defplicit) (Gam ctxt)
>        return $ Ctxt st { defs = newdefs }

> -- | Add a new binary operator on constants. Warning: The type you give
> -- is not checked!
> addBinOp :: (ViewConst a, ViewConst b, ViewConst c, IsTerm ty, Monad m) =>
>             Context -> Name -> (a->b->c) -> ty -> m Context
> addBinOp (Ctxt st) n f tyin = do
>        checkNotExists n (defs st)
>        Term (ty, _) <- Ivor.TT.check (Ctxt st) tyin
>        let fndef = PrimOp mkfun
>        let Gam ctxt = defs st
>        -- let newdefs = Gam ((n,(G fndef ty)):ctxt)
>        newdefs <- gInsert n (G fndef ty defplicit) (Gam ctxt)
>        return $ Ctxt st { defs = newdefs }
>    where mkfun :: Spine Value -> Maybe Value
>          mkfun (Snoc (Snoc Empty (MR (RdConst x))) (MR (RdConst y)))
>              = case cast x of
>                   Just x' -> case cast y of
>                      Just y' -> Just $ MR (RdConst $ f x' y')
>                      Nothing -> Nothing
>                   Nothing -> Nothing
>          mkfun _ = Nothing

> -- | Add a new binary function on constants. Warning: The type you give
> -- is not checked!
> addBinFn :: (ViewConst a, ViewConst b, IsTerm ty, Monad m) =>
>             Context -> Name -> (a->b->ViewTerm) -> ty -> m Context
> addBinFn (Ctxt st) n f tyin = do
>        checkNotExists n (defs st)
>        Term (ty, _) <- Ivor.TT.check (Ctxt st) tyin
>        let fndef = PrimOp mkfun
>        let Gam ctxt = defs st
>        -- let newdefs = Gam ((n,(G fndef ty)):ctxt)
>        newdefs <- gInsert n (G fndef ty defplicit) (Gam ctxt)
>        return $ Ctxt st { defs = newdefs }
>    where mkfun :: Spine Value -> Maybe Value
>          mkfun (Snoc (Snoc Empty (MR (RdConst x))) (MR (RdConst y)))
>              = case cast x of
>                   Just x' -> case cast y of
>                      Just y' -> case Ivor.TT.check (Ctxt st) $ f x' y' of
>                          Just (Term (Ind v,_)) ->
>                              Just $ nf (Gam []) (VG []) [] False v
>                      Nothing -> Nothing
>                   Nothing -> Nothing
>          mkfun _ = Nothing

> -- | Add a new primitive function on constants, usually used for converting
> -- to some form which can be examined in the type theory itself.
> -- Warning: The type you give is not checked!
> addPrimFn :: (ViewConst a, IsTerm ty, Monad m) =>
>             Context -> Name -> (a->ViewTerm) -> ty -> m Context
> addPrimFn (Ctxt st) n f tyin = do
>        checkNotExists n (defs st)
>        Term (ty, _) <- Ivor.TT.check (Ctxt st) tyin
>        let fndef = PrimOp mkfun
>        let Gam ctxt = defs st
>        -- let newdefs = Gam ((n,(G fndef ty)):ctxt)
>        newdefs <- gInsert n (G fndef ty defplicit) (Gam ctxt)
>        return $ Ctxt st { defs = newdefs }
>    where mkfun :: Spine Value -> Maybe Value
>          mkfun (Snoc Empty (MR (RdConst x)))
>              = case cast x of
>                   Just x' -> case Ivor.TT.check (Ctxt st) $ f x' of
>                                  Just (Term (Ind v,_)) ->
>                                      Just $ nf (Gam []) (VG []) [] False v
>                                  Nothing -> Nothing
>                   Nothing -> Nothing
>          mkfun _ = Nothing

> -- | Add a new externally defined function.
> -- Warning: The type you give is not checked!
> addExternalFn :: (IsTerm ty, Monad m) =>
>                  Context -> Name -> Int -- ^ arity
>                  -> ([ViewTerm] -> Maybe ViewTerm) -- ^ The function, which must
>                     -- accept a list of the right length given by arity.
>                  -> ty -> m Context
> addExternalFn (Ctxt st) n arity f tyin = do
>        checkNotExists n (defs st)
>        Term (ty, _) <- Ivor.TT.check (Ctxt st) tyin
>        let fndef = PrimOp mkfun
>        let Gam ctxt = defs st
>        -- let newdefs = Gam ((n,(G fndef ty)):ctxt)
>        newdefs <- gInsert n (G fndef ty defplicit) (Gam ctxt)
>        return $ Ctxt st { defs = newdefs }
>    where mkfun :: Spine Value -> Maybe Value
>          mkfun sx | xs <- listify sx
>            = if (length xs) /= arity then Nothing
>               else case runf xs of
>                      Just res ->
>                          case (Ivor.TT.check (Ctxt st) res) of
>                             Nothing -> Nothing
>                             Just (Term (Ind tm, _)) -> 
>                                 Just $ nf (Gam []) (VG []) [] False tm
>                      Nothing -> Nothing

Using 'Star' here is a bit of a hack; I don't want to export vt from
ViewTerm, and I don't want to cut&paste code, and it's thrown away anyway...
Slightly annoying, but we'll cope.

>          runf spine = f (map viewValue spine) 
>          viewValue x = view (Term (Ind (forget ((quote x)::Normal)), 
>                                 Ind TTCore.Star))


> -- |Add implicit binders for names used in a type, but not declared.
> -- |Returns the new type and the number of implicit names bound.

Search for all unbound names and reverse the list so that we bind them
in left to right order. (Not that this really matters but I find it more
intuitive)

> addImplicit :: Context -> ViewTerm -> (Int, ViewTerm)
> addImplicit ctxt tm = bind 0 (reverse (namesIn tm)) tm
>   where bind i [] tm = (i,tm)
>         bind i (n:ns) tm | defined ctxt n = bind i ns tm
>                          | otherwise = bind (i+1) ns 
>                                           (Forall n Placeholder tm)

> -- |Begin a new proof.
> theorem :: (IsTerm a, Monad m) => Context -> Name -> a -> m Context
> theorem (Ctxt st) n tm = do 
>        checkNotExists n (defs st)
>        rawtm <- raw tm
>        (tv,tt) <- tcClaim (defs st) rawtm
>        case (proofstate st) of
>            Nothing -> do 
>                       let thm = Tactics.theorem n tv
>                       attack defaultGoal 
>                                  $ Ctxt st { proofstate = Just $ thm,
>                                              holequeue = [n],
>                                              hidden = []
>                                              }
>            (Just t) -> fail "Already a proof in progress"

> -- |Begin a new interactive definition.
> -- Actually, just the same as 'theorem' but this version allows you to
> -- make recursive calls, which should of course be done with care.
> interactive :: (IsTerm a, Monad m) => Context -> Name -> a -> m Context
> interactive (Ctxt st) n tm = do 
>        checkNotExists n (defs st)
>        (Ctxt st') <- declare (Ctxt st) n tm
>        rawtm <- raw tm
>        (tv,tt) <- tcClaim (defs st) rawtm
>        case (proofstate st) of
>            Nothing -> do 
>                       let thm = Tactics.theorem n tv
>                       attack defaultGoal 
>                                  $ Ctxt st' { proofstate = Just $ thm,
>                                               holequeue = [n],
>                                               hidden = []
>                                               }
>            (Just t) -> fail "Already a proof in progress"

> -- |Suspend the current proof. Clears the current proof state; use 'resume'
> -- to continue the proof.
> suspend :: Context -> Context
> suspend (Ctxt st) = case (suspendProof st) of
>                        (Just st') -> Ctxt st'
>                        Nothing -> Ctxt st

> -- |Resume an unfinished proof, suspending the current one if necessary. 
> -- Fails if there is no such name. Can also be used to begin a 
> -- proof of an identifier previously claimed as an axiom.
> -- Remember that you will need to 'attack' the goal if you are resuming an
> -- axiom.
> resume :: Monad m => Context -> Name -> m Context
> resume ctxt@(Ctxt st) n = 
>     case glookup n (defs st) of
>         Just ((Ivor.Nobby.Partial _ _),_) -> do let (Ctxt st) = suspend ctxt
>                                                 st' <- resumeProof st n
>                                                 return (Ctxt st')
>         Just (Unreducible,ty) -> 
>             do let st' = st { defs = remove n (defs st) }
>                theorem (Ctxt st') n (Term (ty, Ind TTCore.Star))
>         _ -> fail "No such suspended proof"

> -- | Freeze a name (i.e., set it so that it does not reduce)
> -- Fails if the name does not exist.
> freeze :: Monad m => Context -> Name -> m Context
> freeze (Ctxt st) n 
>      = case glookup n (defs st) of
>           Nothing -> fail $ show n ++ " is not defined"
>           _ -> return $ Ctxt st { defs = Ivor.Nobby.freeze n (defs st) }

> -- | Unfreeze a name (i.e., allow it to reduce).
> -- Fails if the name does not exist.
> thaw :: Monad m => Context -> Name -> m Context
> thaw (Ctxt st) n
>      = case glookup n (defs st) of
>           Nothing -> fail $ show n ++ " is not defined"
>           _ -> return $ Ctxt st { defs = Ivor.Nobby.thaw n (defs st) }


> -- | Save the state (e.g. for Undo)
> save :: Context -> Context
> save (Ctxt st) = Ctxt $ saveState st

> -- | Clears the saved state (e.g. if undo no longer makes sense, like when
> -- a proof has been completed)
> clearSaved :: Context -> Context
> clearSaved (Ctxt st) = Ctxt st { undoState = Nothing }

> -- | Restore a saved state; fails if none have been saved.
> restore :: Monad m => Context -> m Context
> restore (Ctxt st) = case undoState st of
>                        Nothing -> fail "No saved state"
>                        (Just st') -> return $ Ctxt st'


Give a parseable but ugly representation of a term.

> uglyPrint :: ViewTerm -> String
> uglyPrint t = show (forget t)

 -- |Parse and typecheck a term
 newTerm :: Monad m => Context -> String -> m Term
 newTerm (Ctxt st) str = do 
     case (parseterm str) of
         Success raw -> do (tm,ty) <- typecheck (defs st) raw
                           return $ Term (tm, ty)
         Failure err -> fail err

> -- |Normalise a term and its type
> eval :: Context -> Term -> Term
> eval (Ctxt st) (Term (tm,ty)) = Term (normalise (defs st) tm,
>                                       normalise (defs st) ty)

> -- |Reduce a term and its type to Weak Head Normal Form
> whnf :: Context -> Term -> Term
> whnf (Ctxt st) (Term (tm,ty)) = Term (eval_whnf (defs st) tm,
>                                          eval_whnf (defs st) ty)

> -- |Check a term in the context of the given goal
> checkCtxt :: (IsTerm a, Monad m) => Context -> Goal -> a -> m Term
> checkCtxt (Ctxt st) goal tm =
>     do rawtm <- raw tm
>        prf <- case proofstate st of
>                 Nothing -> fail "No proof in progress"
>                 Just x -> return x
>        let h = case goal of
>                (Goal x) -> x
>                DefaultGoal -> head (holequeue st)
>        case (Tactics.findhole (defs st) (Just h) prf holeenv) of
>          (Just env) -> do t <- Ivor.Typecheck.check (defs st) env rawtm Nothing
>                           return $ Term t
>          Nothing -> fail "No such goal"
>  where holeenv :: Gamma Name -> Env Name -> Indexed Name -> Env Name
>        holeenv gam hs _ = Tactics.ptovenv hs

> -- |Evaluate a term in the context of the given goal
> evalCtxt :: (IsTerm a, Monad m) => Context -> Goal -> a -> m Term
> evalCtxt (Ctxt st) goal tm =
>     do rawtm <- raw tm
>        prf <- case proofstate st of
>                 Nothing -> fail "No proof in progress"
>                 Just x -> return x
>        let h = case goal of
>                (Goal x) -> x
>                DefaultGoal -> head (holequeue st)
>        case (Tactics.findhole (defs st) (Just h) prf holeenv) of
>          (Just env) -> do (tm, ty) <- Ivor.Typecheck.check (defs st) env rawtm Nothing
>                           let tnorm = normaliseEnv env (defs st) tm
>                           return $ Term (tnorm, ty)
>          Nothing -> fail "No such goal"
>  where holeenv :: Gamma Name -> Env Name -> Indexed Name -> Env Name
>        holeenv gam hs _ = Tactics.ptovenv hs


> -- |Check whether the conversion relation holds between two terms, in the
> -- context of the given goal

> converts :: (Monad m, IsTerm a, IsTerm b) => 
>             Context -> Goal -> a -> b -> m Bool
> converts ctxt@(Ctxt st) goal a b 
>     = do atm <- checkCtxt ctxt goal a
>          btm <- checkCtxt ctxt goal b
>          prf <- case proofstate st of
>                 Nothing -> fail "No proof in progress"
>                 Just x -> return x
>          let (Term (av,_)) = atm
>          let (Term (bv,_)) = btm
>          let h = case goal of
>                (Goal x) -> x
>                DefaultGoal -> head (holequeue st)
>          case (Tactics.findhole (defs st) (Just h) prf holeenv) of
>                (Just env) -> case checkConvEnv env (defs st) av bv "" of
>                     Just _ -> return True
>                     _ -> return False
>                Nothing -> fail "No such goal"
>  where holeenv :: Gamma Name -> Env Name -> Indexed Name -> Env Name
>        holeenv gam hs _ = Tactics.ptovenv hs

> -- |Lookup a definition in the context.
> getDef :: Monad m => Context -> Name -> m Term
> getDef (Ctxt st) n = case glookup n (defs st) of
>                         Just ((Fun _ tm),ty) -> return $ Term (tm,ty)
>                         _ -> fail "Not a function name"

> -- |Check whether a name is defined
> defined :: Context -> Name -> Bool
> defined (Ctxt st) n = case glookup n (defs st) of
>                          Just _ -> True
>                          _ -> False

> -- |Lookup a pattern matching definition in the context.
> getPatternDef :: Monad m => Context -> Name -> m Patterns
> getPatternDef (Ctxt st) n 
>     = case glookup n (defs st) of
>           Just ((PatternDef pmf),ty) -> 
>               return $ Patterns (map mkPat (getPats pmf))
>           Nothing -> fail "Not a pattern matching definition"
>    where getPats (PMFun _ ps) = ps
>          mkPat (Sch ps ret) = PClause (map viewPat ps) (view (Term (ret, (Ind TTCore.Star))))
>
>          viewPat (PVar n) = Name Bound (name (show n))
>          viewPat (PCon t n ty ts) = VTerm.apply (Name Bound (name (show n))) (map viewPat ts)
>          viewPat (PConst c) = Constant c
>          viewPat _ = Placeholder

> -- |Get all the names and types in the context
> getAllDefs :: Context -> [(Name,Term)]
> getAllDefs (Ctxt st) = let (Gam ds) = defs st in
>                            reverse (map info ds) -- input order!
>    where info (n,G _ ty _) = (n, Term (ty, Ind TTCore.Star))

> -- | Get the names of all of the constructors of an inductive family
> getConstructors :: Monad m => Context -> Name -> m [Name]
> getConstructors (Ctxt st) n 
>      = case glookup n (defs st) of
>           Just ((TCon _ (Elims _ _ cs)),ty) -> return cs
>           _ -> fail "Not a type constructor"

Examine pattern matching elimination rules

> -- | Types of elimination rule
> data Rule = Case | Elim

> -- | Get the pattern matching elimination rule for a type
> getElimRule :: Monad m => Context -> Name -- ^ Type
>                  -> Rule -- ^ Which rule to get patterns for (case or elim)
>                  -> m Patterns
> getElimRule (Ctxt st) nm r = 
>     case (lookupval nm (defs st)) of
>       Just (TCon _ (Elims erule crule cons)) ->
>          do let rule = case r of -- rule :: Name
>                          Case -> crule
>                          Ivor.TT.Elim -> erule
>             elim <- lookupM rule (eliminators st)
>             return $ Patterns $ map mkRed (fst $ snd elim)
>       Nothing -> fail $ (show nm) ++ " is not a type constructor"
>  where mkRed (RSch pats ret) = PClause (map viewRaw pats) (viewRaw ret)
>         -- a reduction will only have variables and applications
>        viewRaw (Var n) = Name Free n
>        viewRaw (RApp f a) = VTerm.App (viewRaw f) (viewRaw a)
>        viewRaw _ = VTerm.Placeholder

Get the actions performed by the last tactic

 getActions :: Context -> [Tactics.TacticAction]
 getActions (Ctxt st) = actions st

> getResponse :: Context -> String
> getResponse (Ctxt st) = response st

> -- |Get the goals still to be solved.
> getGoals :: Context -> [Goal]
> getGoals (Ctxt st) = map Goal (holequeue st)

> -- |Return whether all goals have been solved.
> allSolved :: Context -> Bool
> allSolved (Ctxt st) = null $ holequeue st

> -- |Get the number of unsolved goals
> numUnsolved :: Context -> Int
> numUnsolved (Ctxt st) =
>     case proofstate st of
>         Nothing -> 0
>         (Just t) -> length $ Tactics.allholes (defs st) False t

> -- |Return whether we are in the middle of proving something.
> proving :: Context -> Bool
> proving (Ctxt st) = case proofstate st of
>                        Nothing -> False
>                        _ -> True

> -- |Get the current proof term, if we are in the middle of a proof.
> proofterm :: Monad m => Context -> m Term
> proofterm (Ctxt st) = case proofstate st of
>                         Nothing -> fail "No proof in progress"
>                         Just (Ind (Bind _ (B (Guess v) t) _)) -> 
>                             return $ Term (Ind v,Ind t)
>                         Just t -> fail $ "Proof finished; " ++ show t

> -- |Get the type and context of the given goal, if it exists
> getGoal :: Monad m => Context -> Goal -> m ([(Name,Term)], Term)
> getGoal (Ctxt st) goal =
>     let h = case goal of
>                   (Goal x) -> x
>                   DefaultGoal -> head (holequeue st) in
>       case (proofstate st) of
>         Nothing -> fail "No proof in progress"
>         (Just tm) ->
>             case (Tactics.findhole (defs st) (Just h) tm getHoleTerm) of
>               Just x -> return x
>               Nothing -> fail "No such goal"

> getHoleTerm gam hs tm = (getctxt hs, 
>                          Term (normaliseEnv hs (Gam []) (binderType tm), 
>                                Ind TTCore.Star))
>    where getctxt [] = []
>          getctxt ((n,B _ ty):xs) = (n,Term (Ind ty,Ind TTCore.Star)):
>                                    getctxt xs
>          binderType (Ind (Bind _ (B _ ty) _)) = (Ind ty)
>          binderType _ = error "Can't happen (binderType)"

> -- |Environment and goal type for a given subgoal
> data GoalData = GoalData { 
>                  bindings :: [(Name,Term)], 
>                      -- ^ Get the premises of the goal
>                  goalName :: Goal, 
>                      -- ^ Get the name of the goal
>                  goalType :: Term 
>                      -- ^ Get the type of the goal
>                  }


> -- |Get information about a subgoal.
> goalData :: Monad m => Context -> Bool -- ^ Get all bindings (True), or 
>                                        -- just lambda bindings (False)
>          -> Goal -> m GoalData
> goalData (Ctxt st) all goal = case proofstate st of
>         Nothing -> fail "No proof in progress"
>         (Just prf) -> 
>             let h = case goal of
>                           (Goal x) -> x
>                           DefaultGoal -> head (holequeue st) in
>               case (Tactics.findhole (defs st) (Just h) prf holedata) of
>                  (Just x) -> return x
>                  Nothing -> fail "No such goal"
>  where holedata :: Gamma Name -> Env Name -> Indexed Name -> GoalData
>        holedata gam hs tm = hd' (Tactics.ptovenv hs) (finalise tm) -- (normaliseEnv hs (Gam []) (finalise tm))
>        hd' hs (Ind (Bind n (B _ tm) _))
>            = GoalData (getbs hs) (Goal n)
>                  (Term (Ind tm,
>                         (Ind TTCore.Star)))
>        getbs [] = []
>        getbs ((n,B b ty):xs) 
>            | (b == TTCore.Lambda || all) && (not (n `elem` (hidden st)))
>                = (n, (Term (Ind ty, Ind TTCore.Star))):
>                  getbs xs
>        getbs (_:xs) = getbs xs

> -- | Get the names and types of all goals
> subGoals :: Monad m => Context -> m [(Name,Term)]
> subGoals (Ctxt st) = case proofstate st of
>         Nothing -> fail "No proof in progress"
>         (Just prf) -> return $ 
>                        map (\ (x,ty) -> (x,Term (ty,Ind TTCore.Star)))
>                         $ Tactics.allholes (defs st) True prf

> -- | Create a name unique in the proof state
> uniqueName :: Monad m => Context -> Name -- ^ Suggested name
>            -> m Name -- ^ Unique name based on suggested name
> uniqueName (Ctxt st) n = case proofstate st of
>         Nothing -> fail "No proof in progress"
>         (Just (Ind prf)) -> return $ uniqify n $ getBoundNames (Sc prf)

Tactics

 newTheorem :: Monad m => Context -> Name -> String -> m Context
 newTheorem (Ctxt st) n str = do
    rawtm <- case parseterm str of
                    (Success x) -> return x
                    (Failure err) -> fail err
    (tv,tt) <- tcClaim (defs st) rawtm
    case (proofstate st) of
        Nothing -> do let thm = Tactics.theorem n tv
                      (start, _) <- Tactics.runtactic (defs st) n thm 
                                       (Tactics.attack (fH tt))
                      return $ Ctxt st { proofstate = Just $ start,
                                         holequeue = 
                                             (fH tt):n:(holequeue st) }
        (Just t) -> fail "Already a proof in progress"
   where fH (Ind tt) = uniqify (UN "H") [n]


> -- |Lift a finished proof into the context
> qed :: Monad m => Context -> m Context
> qed (Ctxt st)
>     = do case proofstate st of
>            Just prf -> do
>              newdef@(name,val@(G (Fun _ ind) _ _)) <- 
>                  qedLift (defs st) False prf
>              let isrec = rec name
>              let (Gam olddefs) = remove name (defs st)
>              let runtts = runtt st
>              let scs = lift name (levelise (normalise (Gam []) ind))
>              let bc = compileAll (runtts++scs) scs
>              let newbc = bc++(bcdefs st)
>              defs' <- gInsert name val (defs st)
>              let newdefs = setRec name isrec defs'
>              return $ Ctxt st { proofstate = Nothing, 
>                             bcdefs = newbc,
>                             runtt = runtts ++ scs,
>                             defs = newdefs } -- Gam (newdef:olddefs) }
>            Nothing -> fail "No proof in progress"
>  where rec nm = case lookupval nm (defs st) of
>                   Nothing -> False
>                   _ -> True

> qedLift :: Monad m => Gamma Name -> Bool -> Indexed Name -> 
>                       m (Name, Gval Name)
> qedLift gam freeze 
>             (Ind (Bind x (B (TTCore.Let v) ty) (Sc (P n)))) | n == x =
>     do let (Ind vnorm) = convNormalise (Gam []) (finalise (Ind v))
>        verify gam (Ind v)
>        return $ (x, G (Fun opts (Ind vnorm)) (finalise (Ind ty)) defplicit)
>   where opts = if freeze then [Frozen] else []
> qedLift _ _ tm = fail $ "Not a complete proof " ++ show tm

> -- | Focus on a different hole, i.e. set the default goal.
> focus :: Tactic
> focus (Goal n) (Ctxt st)
>    | n `elem` holequeue st 
>        = attack (Goal n) $ Ctxt st { holequeue = jumpqueue n (holequeue st) }
>    | otherwise = fail "No such goal"
> focus _ x = return x -- Default goal already first

> -- | Hide a premise
> hide :: Tactic
> hide (Goal n) (Ctxt st)
>    = return $ Ctxt st { hidden = nub (n:(hidden st)) }

> -- | The Identity tactic, does nothing.
> idTac :: Tactic
> idTac goal ctxt = return ctxt

> -- | The Tracing tactic; does nothing, but uses 'trace' to dump the
> -- current proof state
> traceTac :: Tactic
> traceTac goal ctxt@(Ctxt st) = trace ("Proofstate: " ++ 
>                                       (show (proofstate st) ++ "\nHoles" ++ 
>                                       (show (holequeue st)))) $ return ctxt

> infixl 5 >->, >=>, >+>, >|>

Apply two tactics consecutively to the same goal.

> seqTac :: Tactic -> Tactic -> Tactic
> seqTac tac1 tac2 goalin ctxt@(Ctxt st) = do
> -- In case the default goal changes, remember where we are
>     let goal = case goalin of 
>                     DefaultGoal -> Goal $ head (holequeue st)
>                     x -> x
>     ctxt' <- tac1 goal ctxt
>     tac2 goal ctxt'

> -- | Sequence two tactics; applies two tactics sequentially to the same goal
> (>->) :: Tactic -> Tactic -> Tactic 
> (>->) x y = seqTac x y

> thenTac :: Tactic -> Tactic -> Tactic
> thenTac tac1 tac2 goal ctxt@(Ctxt st) = do
>     let hq = holequeue st
>     (Ctxt st') <- tac1 goal ctxt
>     let newholes = (holequeue st') \\ hq
>     -- Why reverse? Because then the new hole queue is the right order.
>     runThen (map Goal (reverse newholes)) tac2 (Ctxt st')
>   where runThen [] _ ctxt = return ctxt
>         runThen (x:xs) tac ctxt = do ctxt' <- tac x ctxt
>                                      runThen xs tac ctxt'

> -- | Apply a tactic, then apply another to each subgoal generated.
> (>=>) :: Tactic -> Tactic -> Tactic 
> (>=>) x y = thenTac x y


> nextTac :: Tactic -> Tactic -> Tactic
> nextTac tac1 tac2 goal ctxt = do
>     ctxt' <- tac1 goal ctxt
>     tac2 DefaultGoal ctxt'

> -- | Apply a sequence of tactics to the default goal. Read the type
> -- as ['Tactic'] -> 'Tactic'
> tacs :: Monad m => [Goal -> Context -> m Context] -> 
>         Goal -> Context -> m Context
> tacs [] = idTac
> tacs (t:ts) = \g ctxt -> do ctxt <- t g ctxt
>                             tacs ts DefaultGoal ctxt

> -- | Apply a tactic, then apply the next tactic to the next default subgoal.
> (>+>) :: Tactic -> Tactic -> Tactic 
> (>+>) x y = nextTac x y

> -- | Try a tactic.
> try :: Tactic -- ^ Tactic to apply
>     -> Tactic -- ^ Apply if first tactic succeeds
>     -> Tactic -- ^ Apply if first tactic fails. 
>     -> Tactic
> try tac success failure goal ctxt = 
>     case tac goal ctxt of
>         Just ctxt' -> success goal ctxt'
>         Nothing -> failure goal ctxt

> -- | Tries the left tactic, if that fails try the right one. Shorthand for
> -- 'try' x 'idTac' y.
> (>|>) :: Tactic -> Tactic -> Tactic
> (>|>) x y = try x idTac y

Convert an internal tactic into a publicly available tactic.

> runTac :: Tactics.Tactic -> Tactic
> runTac tac goal (Ctxt st) | null (holequeue st) = fail "No more goals"
> runTac tac goal (Ctxt st) = do
>     let hole = case goal of
>                     (Goal x) -> x
>                     DefaultGoal -> head (holequeue st)
>     let (Just prf) = proofstate st
>     (prf', act) <- Tactics.runtactic (defs st) hole prf tac
>     let st' = addgoals act st
>     return $ Ctxt st' { proofstate = Just prf',
>                         --holequeue = jumpqueue hole 
>                         --       (holequeue st'),
>                         actions = act
>                       }
>     where addgoals [] st = st
>           addgoals ((Tactics.AddGoal n):xs) st
>               = addgoals xs (st { holequeue = nub (n:(holequeue st)) })
>           addgoals ((Tactics.NextGoal n):xs) st 
>               = addgoals xs (st { holequeue = nub (second n (holequeue st)) })
>           addgoals ((Tactics.AddAxiom n ty):xs) st
>               = let Gam ctxt = defs st in
>                     addgoals xs (st 
>                        { defs = Gam ((n,G Unreducible (finalise (Ind ty)) defplicit):ctxt) })
>           addgoals ((Tactics.HideGoal n):xs) st
>               = addgoals xs (st { hidden = nub (n:(hidden st)) })
>           addgoals (_:xs) st = addgoals xs st
>           second n (x:xs) = x:n:xs
>           second n [] = [n]

> -- | Prepare a goal for introduction.
> attackWith :: Name -- ^ Name for new goal
>            -> Tactic
> attackWith n goal ctxt = 
>     do (Ctxt st) <- runTac (Tactics.attack n) goal ctxt
>        return $ Ctxt st { holequeue = nub (n:(holequeue st)) }

> -- | Prepare a goal for introduction.
> attack :: Tactic
> attack goal (Ctxt st) = do n <- getName
>                            attackWith n goal (Ctxt st)
>    where getName = do allnames <- case (proofstate st) of
>                             Nothing -> fail "No proof in progress"
>                             Just (Ind tm) -> 
>                                 return $ binderMap (\n _ _ -> n) tm
>                       return $ uniqify (name "H") ((holequeue st)++allnames)

> -- | Make a local claim
> claim :: IsTerm a => Name -> a -> Tactic
> claim name ty = claim' name ty >+> keepSolving
> claim' name ty g ctxt = do rawty <- raw ty
>                            name' <- uniqueName ctxt name
>                            runTac (Tactics.claim name' rawty) g ctxt

> -- | Solve a goal by applying a function.
> -- If the term given has arguments, attempts to fill in these arguments
> -- by unification and solves them (with 'solve').
> -- See 'refineWith' and 'basicRefine' for slight variations.
> refine :: IsTerm a => a -> Tactic
> refine tm = (basicRefine tm >=> trySolve) >+> keepSolving

> -- | Solve a goal by applying a function.
> -- If the term given has arguments, this will create a subgoal for each.
> -- Some arguments may be solved by unification, in which case they will
> -- already have a guess attached after refinement, but the guess will not
> -- be solved (via 'solve').
> basicRefine :: IsTerm a => a -> Tactic
> basicRefine tm = do rawtm <- raw tm
>                     runTac (Tactics.refine rawtm [])

> -- | Solve a goal by applying a function with some arguments filled in.
> -- See 'refine' for details.
> refineWith :: IsTerm a => a -> [a] -> Tactic
> refineWith tm args = (refineWith' tm args >=> trySolve) >+> keepSolving

> refineWith' tm args = do rawtm <- raw tm
>                          rawargs <- mapM raw args
>                          runTac (Tactics.refine rawtm rawargs)

> -- | Finalise a goal's solution.
> solve :: Tactic
> solve goal ctxt 
>     = do (Ctxt st') <- runTac (Tactics.solve) goal ctxt
>          return $ Ctxt st' { holequeue = 
>                                  removeGoal goal (holequeue st') }
>   where removeGoal DefaultGoal xs = stail xs
>         removeGoal (Goal x) xs = xs \\ [x]

> -- | If the goal has a solution, finalise it, otherwise prepare the
> -- goal (with attack).
> -- Typically, could be used on the subgoals generated by refinement, where
> -- some may have solutions attached already, and others will need to be
> -- prepared.
> trySolve :: Tactic
> trySolve = try solve idTac attack

> -- | Finalise as many solutions of as many goals as possible.
> keepSolving :: Tactic
> keepSolving goal ctxt 
>     | allSolved ctxt = return ctxt
> keepSolving goal ctxt = trySolve (getGoals ctxt) ctxt
>    where trySolve [] ctxt = return ctxt
>          trySolve (x:xs) ctxt 
>              = case solve x ctxt of
>                   Just ctxt' -> trySolve xs ctxt'
>                   Nothing -> trySolve xs ctxt

-- > keepSolving goal ctxt 
-- >   | not (null (getGoals ctxt)) =
-- >     case solve goal ctxt of
-- >        (Just ctxt') -> keepSolving defaultGoal ctxt'
-- >        Nothing -> return ctxt
-- >   | otherwise = return ctxt

> -- | Attach a solution to a goal.
> fill :: IsTerm a => a -> Tactic
> fill guess = fill' guess >+> keepSolving

> fill' guess = do rawguess <- raw guess
>                  runTac (Tactics.fill rawguess)

> -- | Remove a solution from a goal.
> abandon :: Tactic
> abandon = runTac (Tactics.regret)

> -- | Remove all claims with no guesses attached and which are unused in
> -- their scope.
> tidy :: Tactic
> tidy = runTac (Tactics.tidy)

> -- | Substitute a let bound value into its scope.
> cut :: Tactic
> cut goal ctxt = do (Ctxt st) <- runTac (Tactics.cut) goal ctxt
>                    return $ Ctxt st { holequeue = stail (holequeue st) }

> -- | Rename the outermost binder in the given goal
> rename :: Name -> Tactic
> rename n = runTac (Tactics.rename n)

FIXME: Choose a sensible name here

> -- | Introduce an assumption (i.e. a lambda binding)
> intro :: Tactic
> intro = runTac (Tactics.intro)

> -- | Introduce an assumption (i.e. a lambda binding)
> introName :: Name -- ^ Name for the assumption
>                -> Tactic
> introName n = (rename n >-> intro)

> -- | Keep introducing things until there's nothing left to introduce.
> intros :: Tactic
> intros goal ctxt = do_intros goal ctxt
>   where do_intros :: Tactic
>         do_intros = try intro do_intros idTac

> -- | Keep introducing things until there's nothing left to introduce,
> -- Must introduce at least one thing.
> intros1 :: Tactic
> intros1 goal ctxt = 
>     do ctxt <- intro goal ctxt -- Must be at least one thing
>        do_intros goal ctxt
>   where do_intros :: Tactic
>         do_intros = try intro do_intros idTac

> -- | As 'intros', but with names, and stop when we've run out of names.
> -- Fails if too many names are given.

> introsNames :: [Name] -> Tactic
> introsNames [] = idTac
> introsNames (n:ns) = \goal ctxt ->
>     do ctxt <- introName n goal ctxt
>        introsNames ns goal ctxt

> -- | Check that the goal is definitionally equal to the given term, 
> -- and rewrite the goal accordingly. 
> equiv :: IsTerm a => a -> Tactic
> equiv ty = do rawty <- raw ty
>               runTac (Tactics.equiv rawty)

> -- | Abstract over the given term in the goal.
> generalise :: IsTerm a => a -> Tactic
> generalise tm = generalise' tm >-> attack

> generalise' tm = do rawtm <- raw tm
>                     runTac (Tactics.generalise rawtm)

> -- | Abstract over the given term in the goal, and also all variables
> -- appearing in the goal whose types depend on it.
> dependentGeneralise :: IsTerm a => a -> Tactic
> dependentGeneralise tm = dependentGeneralise' tm

> dependentGeneralise' tm g ctxt = 
>     do gd <- goalData ctxt False g
>        vtm <- checkCtxt ctxt g tm
>        ctxt <- gDeps (filter ((occursIn (view vtm)).(view.snd))
>                                  (bindings gd))
>                   ctxt (view (goalType gd))
>        generalise tm g ctxt
>   where gDeps [] ctxt gty = return ctxt
>         gDeps (x:xs) ctxt gty
>           | freeIn (fst x) gty 
>               = do ctxt <- generalise (Name Free (fst x)) g ctxt
>                    gDeps xs ctxt gty
>           | otherwise = gDeps xs ctxt gty

> -- | Add a new top level argument after the arguments its type depends on
> -- (changing the type of the theorem). This can be useful if, for example,
> -- you find you need an extra premise to prove a goal.
> addArg :: IsTerm a => Name -> a -> Tactic
> addArg n ty g ctxt@(Ctxt st) 
>     = do rawty <- raw ty
>          Term (Ind tm, _) <- checkCtxt ctxt g rawty
>          st' <- Ivor.State.addArg st n tm
>          return $ Ctxt st'

> -- | Replace a term in the goal according to an equality premise. Any
> -- equality type with three arguments is acceptable (i.e. the type, 
> -- and the two values),
> -- provided there are suitable replacement and symmetry lemmas.
> -- Heterogeneous equality as provided by 'addEquality' is acceptable
> -- (if you provide the lemmas!).
> replace :: (IsTerm a, IsTerm b, IsTerm c, IsTerm d) => 
>            a -- ^ Equality type (e.g. @Eq : (A:*)(a:A)(b:A)*@)
>         -> b -- ^ replacement lemma (e.g. @repl : (A:*)(a:A)(b:A)(q:Eq _ a b)(P:(a:A)*)(p:P a)(P b)@)
>         -> c -- ^ symmetry lemma (e.g. @sym : (A:*)(a:A)(b:A)(p:Eq _ a b)(Eq _ b a)@)
>         -> d -- ^ equality premise
>         -> Bool -- ^ apply premise backwards (i.e. apply symmetry)
>         -> Tactic
> replace eq repl sym tm flip = replace' eq repl sym tm flip >+> attack
> replace' eq repl sym tm flip = 
>     do rawtm <- raw tm
>        raweq <- raw eq
>        rawrepl <- raw repl
>        rawsym <- raw sym
>        runTac (Tactics.replace raweq rawrepl rawsym rawtm flip)

> -- | Add an axiom to the global context which would solve the goal, 
> -- and apply it.
> -- FIXME: This tactic doesn't pick up all dependencies on types, but is
> -- okay for simply typed axioms, e.g. equations on Nats.
> axiomatise :: Name -- ^ Name to give axiom
>            -> [Name] -- ^ Premises to pass to axiom
>            -> Tactic
> axiomatise n ns = runTac (Tactics.axiomatise n ns)

> -- | Normalise the goal
> compute :: Tactic
> compute = runTac Tactics.evalGoal

> -- | Beta reduce in the goal
> beta :: Tactic
> beta = runTac Tactics.betaReduce

> -- | Beta reduce the goal, unfolding the given function
> unfold :: Name -> Tactic
> unfold nm = runTac (Tactics.reduceWith nm)

> -- | Prepare to return a value in a computation
> returnComputation :: Tactic
> returnComputation g ctxt = do
>     (_, gtype) <- getGoal ctxt g
>     rtype <- getRType (view gtype)
>     name <- uniqueName ctxt (name "returnval")
>     ctxt <- claim name rtype g ctxt
>     fill (VTerm.Return (Name Bound name)) g ctxt
>  where getRType (VTerm.Label _ _ ty) = return ty
>        getRType _ = fail "Not a labelled type"

> -- | Prepare to return a quoted value
> quoteVal :: Tactic
> quoteVal = runTac Tactics.quote

> -- | Apply an eliminator. 
> by :: IsTerm a => a -- ^ An elimination rule applied to a target.
>        -> Tactic
> by rule = (by' rule >=> attack) >+> keepSolving

> by' rule = do rawrule <- raw rule
>               runTac (Tactics.by rawrule)

> -- | Apply the appropriate induction rule to the term.
> induction :: IsTerm a => a -- ^ target of the elimination
>                -> Tactic
> induction tm = (induction' tm >=> attack) >+> keepSolving

> induction' tm = do rawtm <- raw tm
>                    runTac (Tactics.casetac True rawtm)

> -- | Apply the appropriate case analysis rule to the term.
> -- Like 'induction', but no induction hypotheses generated.
> cases :: IsTerm a => a -- ^ target of the case analysis
>                -> Tactic
> cases tm = (cases' tm >=> attack) >+> keepSolving
> cases' tm = do rawtm <- raw tm
>                runTac (Tactics.casetac False rawtm)

> -- | Find a trivial solution to the goal by searching through the context
> -- for a premise which solves it immediately by refinement
> trivial :: Tactic
> trivial g ctxt 
>     = do gd <- goalData ctxt False g
>          let ps = bindings gd
>          tryall ps g ctxt
>    where tryall [] g ctxt = fail "No trivial solution found"
>          tryall ((x,ty):xs) g ctxt 
>              = do ctxt' <- ((refine (Name Free x)) >|> (fill (Name Free x))
>                                 >|> idTac)  g ctxt
>                   if (numUnsolved ctxt' < numUnsolved ctxt)
>                      then return ctxt'
>                      else tryall xs g ctxt

Spot the allowed recursive calls in a proof state. This is quite basic,
and only spots primitive recursion for the moment, rather than any
particularly cunning induction hypotheses like those living in memos etc.

> data RecAllowed = Rec { flexible :: [Name], -- arguments that can be anything
>                         function :: Name, -- function to call
>                         args :: [ViewTerm], -- arguments to function
>                         hypothesis :: ViewTerm -- hypothesis which calls it
>                       }
>   deriving Show

> allowedrec :: Monad m => Goal -> Context -> m [RecAllowed]
> allowedrec g ctxt = do
>     gd <- goalData ctxt False g
>     return $ findRec $ bindings gd
>  where
>    findRec [] = []
>    findRec ((n,t):ts) = case isCall (Name Bound n) [] (view t) of
>                           Just v -> v:(findRec ts)
>                           _ -> findRec ts

>    isCall n env (VTerm.Label name args _) = Just (Rec env name args n)
>    isCall n env (Forall name _ scope) = isCall n (name:env) scope
>    isCall _ _ _ = Nothing

> -- | Make a recursive call of a computation. The term must be an 
> -- allowed recursive call, identified in the context by having a 
> -- labelled type.

FIXME: This function is horrible. Redo it at some point...

> call :: IsTerm a => a -> Tactic
> call tm g ctxt = do tm <- raw tm
>                     allowed <- allowedrec g ctxt
>                     rec <- {- trace (show allowed) $ -} findRec allowed tm
>                     fill rec g ctxt
>   where 
>     findRec :: Monad m => [RecAllowed] -> Raw -> m ViewTerm
>     findRec [] tm = fail "This recursive call not allowed"
>     findRec ((Rec fs nm args hyp):rs) tm = 
>         case mkRec fs nm args hyp tm of
>            Just x -> return x
>            _ -> findRec rs tm
>     mkRec fs nm args hyp tm = do
>          let (tmf,tmas) = getfa tm []
>          ttmas <- mapM (checkCtxt ctxt g) tmas
>          let vtmas = map view ttmas
>          if (nm==tmf) then do
>             ihargs <- getIH fs args vtmas
>             return $ VTerm.Call nm vtmas (VTerm.apply hyp ihargs)
>           else fail "Not this one"
>     getfa (RApp f a) args = getfa f (a:args)
>     getfa (Var x) args = (x,args)
>     getIH fs [] [] = return []
>     getIH (f:fs) (x:xs) (y:ys) 
>         | Just f == tryvar x = -- x is pi bound, so better get an ih arg.
>                    do ycheck <- checkCtxt ctxt g y
>                       rest <- getIH fs xs ys
>                       return ((view ycheck):rest)
>     getIH fs (x:xs) (y:ys)
>         | tryvareq x y
>              = getIH fs xs ys -- x not pi bound, but names okay.
>     getIH _ _ _ = fail "Not this one" -- Something doesn't match up.

>     tryvar (Name _ x) = Just x
>     tryvar _ = Nothing
>     tryvareq x y = let jx = tryvar x
>                        jy = tryvar y in
>                        jx /= Nothing && jx == jy

> -- | Create a .hs file containing (unreadable) Haskell code implementing
> -- all of the definitions. 
> -- (TODO: Generate a more readable, usable interface)
> compile :: Context -- ^ context to compile
>            -> String -- ^ root of filenames to generate
>            -> IO ()
> compile (Ctxt st) froot
>     = do let hd = mkHeaders (bcdefs st)
>          let ev = mkEval (bcdefs st)
>          let cd = mkCode (bcdefs st)
>          Compiler.compile st froot
>          -- writeFile (froot++".c") $ hd ++ ev ++ cd


