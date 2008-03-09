> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Tactics where

> import Ivor.TTCore
> import Ivor.Typecheck
> import Ivor.Nobby
> import Ivor.Gadgets
> import Ivor.Unify

> import List
> import Maybe
> import Char
> import Debug.Trace

Tactics for manipulating holes (See Conor McBride's thesis for the 
inspiration for many of these).

Tactics may do several things in addition to manipulating the term. These
include adding a new goal, solving other holes, and wanting to add a
new axiom to the context.

> data TacticAction = AddGoal Name
>                   | NextGoal Name
>                   | Solved Name (TT Name)
>                   | AddAxiom Name (TT Name)
>                   | HideGoal Name
>    deriving (Show,Eq)

> type Tactic = Monad m => Gamma Name ->
>                          Env Name -> 
>                          Indexed Name -> 
>                          m (Indexed Name, [TacticAction])

> type HoleFn a = Gamma Name -> Env Name -> Indexed Name -> a

Find a named hole in a term (or the leftmost outermost hole if no name
is given), and do something if/when you get there.  Could be used for,
e.g., applying tactics, displaying a proof context, etc.

> findhole :: Gamma Name -> Maybe Name -> Indexed Name -> 
>             HoleFn a -> Maybe a
> findhole gam n (Ind s) holefn = fh [] s
>     where fh env b@(Bind x (B Hole ty) _)
>               | same x n = Just $ holefn gam env (Ind b)
>           fh env b@(Bind x (B (Guess v) ty) _)
>               | same x n = Just $ holefn gam env (Ind b)
>           fh env (Bind x binder@(B b ty) (Sc s)) =
>               first [fhb env b,
>                      fh env ty,
>                      fh ((x,binder):env) s]
>           fh env (App f s) = first [fh env f, fh env s]
>           fh env (Stage (Quote t)) = fh env t
>           fh env (Stage (Code t)) = fh env t
>           fh env (Stage (Eval t _)) = fh env t
>           fh env (Stage (Escape t _)) = fh env t
>           fh _ _ = fail "No such hole binder"
>
>           fhb env (Let x) = fh env x
>           fhb env (Guess x) = fh env x
>           fhb env _ = Nothing
>
>           first = maybeHead.catMaybes
>           maybeHead (x:xs) = Just x
>           maybeHead _ = Nothing
>
>           same x Nothing = True
>           same x (Just n) = x == n

Boolean indicates whether to return all (True) or just the ones with
no guesses attached (False).

> allholes :: Gamma Name -> Bool -> Indexed Name -> [(Name,Indexed Name)]
> allholes gam guesses (Ind s) = fh [] s
>     where fh env b@(Bind x binder@(B Hole ty) (Sc sc))
>               = [(x,Ind ty)] ++ fh env ty ++ fh ((x,binder):env) sc
>           fh env b@(Bind x binder@(B (Guess v) ty) (Sc sc))
>              | guesses = [(x,Ind ty)] ++ fh env v ++ fh env ty ++ fh ((x,binder):env) sc
>           fh env (Bind x binder@(B b ty) (Sc s)) =
>               fhb env b ++ fh env ty ++ fh ((x,binder):env) s
>           fh env (App f s) = fh env f ++ fh env s
>           fh env (Stage (Quote t)) = fh env t
>           fh env (Stage (Code t)) = fh env t
>           fh env (Stage (Eval t _)) = fh env t
>           fh env (Stage (Escape t _)) = fh env t
>           fh _ _ = []
>
>           -- fhb env (Let x) = fh env x
>           fhb env (Guess x) = fh env x
>           fhb env _ = []

Typecheck a term in the context of the given hole

> holecheck :: Monad m => Name -> Gamma Name -> Indexed Name -> 
>              Raw -> m (Indexed Name, Indexed Name)
> holecheck n gam state raw = case (findhole gam (Just n) state docheck) of
>                                Nothing -> fail "No such hole binder"
>                                (Just x) -> x
>    where docheck gam env _ = check gam env raw Nothing

Run a tactic on the given named hole (or the first hole, if no name is
given). Searches through the given term for a hole with the given
name, and runs the tactic on the term it finds, with the term in its
appropriate context.

[I wanted to write this in terms of findhole, but then I lose the rest of
the term. Oh well.]

FIXME: Why not use a state monad for the unified variables in rt?

> runtactic :: Monad m => Gamma Name -> Name -> 
>              Indexed Name -> Tactic -> m (Indexed Name, [TacticAction])
> runtactic gam n t tac = runtacticEnv gam [] n t tac

> runtacticEnv :: Monad m => Gamma Name -> Env Name -> Name -> 
>                 Indexed Name -> Tactic -> m (Indexed Name, [TacticAction])
> runtacticEnv gam env n (Ind s) tactic = 
>     do (tm, actions) <- (rt env s)
>        return ((Ind (substNames (mapMaybe mkUnify actions) tm)), actions)
>     where rt env b@(Bind x (B Hole ty) _)
>               | x == n = do (Ind b', u) <- tactic gam env (Ind b)
>                             return (b', u)
>           rt env b@(Bind x (B (Guess v) ty) _)
>               | x == n = do (Ind b',u) <- tactic gam env (Ind b)
>                             return (b', u)
>           rt env b@(Bind x (B (Let v) ty) _)
>               | x == n = do (Ind b',u) <- tactic gam env (Ind b)
>                             return (b',u)

                | otherwise = return (b, []) -- fail "No such hole"

>           rt env b@(Bind x (B Lambda ty) _)
>               | x == n = do (Ind b',u) <- tactic gam env (Ind b)
>                             return (b',u)
>           rt env (Bind x binder@(B b ty) (Sc s)) =
>               do (b',u) <- rtb env b
>                  (ty',u') <- rt env ty
>                  (s',u'') <- rt ((x,binder):env) s
>                  return (Bind x (B b' ty') (Sc s'), nub (u++u'++u''))
>           rt env (App f s) = 
>               do (f',u) <- rt env f
>                  (s',u') <- rt env s
>                  return (App f' s', nub (u++u'))
>           rt env (Stage (Quote t)) = do (t',u) <- rt env t
>                                         return (Stage (Quote t'), u)
>           rt env (Stage (Code t)) = do (t',u) <- rt env t
>                                        return (Stage (Code t'), u)
>           rt env (Stage (Eval t ty)) = do (t',u) <- rt env t
>                                           (ty',u) <- rt env ty
>                                           return (Stage (Eval t' ty'), u)
>           rt env (Stage (Escape t ty)) = do (t',u) <- rt env t
>                                             (ty',u) <- rt env ty
>                                             return (Stage (Escape t' ty'), u)
>           rt env x = return (x, [])
>
>           -- No holes in let bound values!
>           --rtb env (Let x) = do (rtx, u) <- rt env x
>           --                     return (Let rtx, u)
>           rtb env (Guess x) = do (rtx, u) <- rt env x
>                                  return (Guess rtx, u)
>           rtb env b = return (b, [])
>           mkUnify (Solved x ty) = Just (x, ty)
>           mkUnify _ = Nothing

Tactics by default don't need to return the other holes they solved.

> tacret :: Monad m => Indexed Name -> m (Indexed Name, [TacticAction])
> tacret x = return (x,[])

Sequence two tactics

> thenT :: Tactic -> Tactic -> Tactic
> thenT tac1 tac2 gam env tm = do (tm',u) <- tac1 gam env tm
>                                 (tm'',u') <- tac2 gam env tm'
>                                 return (tm',nub (u++u'))

Try to run a tactic, do nothing silently if it fails.

> attempt :: Tactic -> Tactic
> attempt tac gam env tm =
>     case tac gam env tm of
>        Just (tm',act) -> return (tm',act)
>        Nothing -> tacret tm

Create a new theorem ?x:S. x

> theorem :: Name -> Indexed Name -> Indexed Name
> theorem x (Ind s) = Ind (Bind x (B Hole s) (Sc (P x)))

Create a new definition with holes ?x:S = holey in x

> makeholey :: Name -> Indexed Name -> Indexed Name -> Indexed Name
> makeholey x (Ind holey) (Ind ty) =
>     Ind (Bind x (B (Guess holey) ty) (Sc (P x)))

Add a new claim to the current state

> claim :: Name -> Raw -> Tactic -- ?Name:Type. 
> claim x s gam env (Ind t) = 
>     do (Ind sv, st) <- check gam (ptovenv env) s Nothing
>        checkConv gam st (Ind Star) "Type of claim must be *"
>        return $ (Ind (Bind x (B Hole (makePsEnv (map fst env) sv)) (Sc t)),
>                      [NextGoal x])

Add a new claim with guess to the current state
[FIXME: Doesn't work yet, should put new goal at the end.]

> claimholey :: Name -> Indexed Name -> Indexed Name -> Tactic
> claimholey x (Ind holey) (Ind ty) gam env (Ind term) =
>     tacret $ Ind (Bind x (B (Guess holey) ty) (Sc term))

> claimsolved :: Name -> Indexed Name -> Indexed Name -> Tactic
> claimsolved x (Ind holey) (Ind ty) gam env (Ind term) =
>     tacret $ Ind (Bind x (B (Let holey) ty) (Sc term))

Begin solving a goal

> attack :: Name -> Tactic
> attack h gam env (Ind (Bind x b@(B Hole ty) sc))
>         = tacret $ Ind (Bind x (B (Guess newtm) ty) sc)
>   where newtm = Bind h0 (B Hole ty) (Sc (P h0))
>         h0 = uniqify h (x:(map fst env))
> attack _ _ _ t = fail $ "Internal error; not an attackable hole: " ++ show t

Try filling the current goal with a term

> fill :: Raw -> Tactic
> fill guess gam env (Ind (Bind x (B Hole tyin') sc)) = 
>     do let (Ind tyin) = finalise (Ind tyin')
>        (Ind gvin,Ind gtin, env) <- {-trace ("checking "++show guess++" in context " ++ show (ptovenv env)) $ -}
>                               checkAndBind gam (ptovenv env) guess (Just (Ind tyin))
>        let gv = makePsEnv (map fst env) gvin
>        let gt = makePsEnv (map fst env) gtin
>        let (Ind ty') = normaliseEnv (ptovenv env) (Gam []) (Ind tyin)
>        let (Ind ty) = normaliseEnv (ptovenv env) gam (Ind tyin)
>        let fgt = finalise (Ind gt)
>        let fty' = finalise (Ind ty')
>        let fty = finalise (Ind ty)
>        others <- -- trace ("unifying "++show gt++" and "++show ty') $
>                  case unifyenv (Gam []) (ptovenv env) fgt fty' of
>                     Nothing -> unifyenv gam (ptovenv env) fgt fty
>                     (Just x) -> return x
>        -- let newgt = substNames others gt
>        -- let newgv = substNames others gv
>        let newgv = gv
>        -- trace ((show others) ++ ", "++ show (Ind newgt)) $ checkConv gam (Ind gt) (Ind ty) $ "Guess is badly typed ("++show gt++", "++show ty++")"
>        return $ (Ind (Bind x (B (Guess newgv) ty) sc), 
>                      map mkAction (nodups others))
>    where pToVs i [] gv = gv
>          pToVs i ((x,_):xs) gv = {- trace ("pToVing "++show x++", " ++ show i++ " in "++show gv) $ -}
>              let (Sc gv') = pToV2 i x gv in
>                  pToVs (i+1) xs gv'
>          mkAction (x,tm) = Solved x tm
>          nodups [] = []
>          nodups ((x,y):xs) | x `elem` (map fst xs) = nodups xs
>                            | otherwise = (x,y):(nodups xs)
> fill _ _ _ _ = fail "Can't try to fill something which isn't a hole"

Use defaults to fill in arguments which don't appear in the goal (hence aren't
solvable by unification). (FIXME: Not yet implemented.)

> refine :: Raw -> [Raw] -> Tactic
> refine rtm defaults gam env tm@(Ind (Bind x (B Hole ty) (Sc sc))) = 
>     do (Ind bv,Ind ntyin) <- check gam (ptovenv env) rtm Nothing
>        let (Ind nty) = normaliseEnv (ptovenv env) gam (Ind ntyin)
>        let bvin = makePsEnv (map fst env) bv
>        -- let (Just (Ind nty)) = lookuptype n gam
>        let claimTypes = getClaims (makePsEnv (map fst env) nty)
>        let rawapp = mkapp rtm (map (\_ -> RInfer) claimTypes)
>        let (Ind tyin') = finalise (normaliseEnv (ptovenv env) gam (Ind ty))
>        (Ind rtch, rtych, ev) <- checkAndBind gam (ptovenv env) rawapp (Just (Ind tyin'))
>        let argguesses = getArgs rtch
>        -- So we'll have an application, some of the arguments with inferred
>        -- names. Let's record which ones...
>        let claims = uniqifyClaims x env claimTypes
>        let claimGuesses = zip claims (map appVar argguesses)
>        (tm',_) <- {- trace (show claimGuesses) $ -} doClaims x claimGuesses gam env tm
>        let guess = (mkGuess claimGuesses [] (forget bvin))
>        (filled, unified) <- runtacticEnv gam env x tm' 
>                  (fill guess)
>        -- (filled, solved) <- solveUnified [] unified filled
>        -- filled <- tryDefaults defaults claims filled
>        -- (tm', _) <- trace (show claims) $ tidy gam env filled
>        let newgoals = mapMaybe isGoal claimGuesses
>        return $ (filled, map HideGoal (map fst claims) ++ 
>                          map AddGoal (reverse newgoals))
>        --                  map AddGoal (map fst (reverse claims)))
>        -- tacret filled --(Ind (Bind x (B Hole ty) (Sc sc')))
>   where mkGuess [] defs n = n
>         mkGuess (((x,_),guess):xs) (RInfer:ds) n 
>             = (mkGuess xs ds (RApp n (Var x)))
>         mkGuess (((x,_),guess):xs) [] n 
>             = (mkGuess xs [] (RApp n (Var x)))
>         -- FIXME: Fix this so default arguments use the 'guess'
>         mkGuess (((x,_),_):xs) (d:ds) n 
>             = (mkGuess xs ds (RApp n d))

>         -- if we inferred a guess, use that, otherwise use the claim name
>         appVar (P (MN ("INFER",_))) = Nothing
>         appVar guess = Just guess
>         isGoal ((n,ty),Nothing) = Just n
>         isGoal ((n,ty),Just _) = Nothing

>         todo uns (x,_) = not (isSolved x uns)
>         solveUnified tohide [] tm = return (tm, tohide)
>         solveUnified tohide ((Solved x guess):xs) tm 
>             = do (filled,_) <- runtacticEnv gam env x tm (fill (forget guess))
>                  solveUnified (x:tohide) xs filled
>         solveUnified tohide (_:xs) tm = solveUnified tohide xs tm
>         isSolved x [] = False
>         isSolved x ((Solved n _):xs) | x==n = True
>         isSolved x (_:xs) = isSolved x xs
>         tryDefaults [] _ f = return f
>         tryDefaults (RInfer:xs) (c:cs) tm
>             = do tryDefaults xs cs tm
>         tryDefaults (x:xs) ((c,ty):cs) tm
>             = do (filled, _) <- runtacticEnv gam env c tm (fill x)
>                  (filled, _) <- runtacticEnv gam env c filled solve
>                  (filled, _) <- runtacticEnv gam env c filled cut
>                  tryDefaults xs cs filled
>         removeClaims claims tm@(Ind (Bind x b@(B _ ty) (Sc sc)))
>             | x `elem` (map fst claims)
>                  = {- trace (show (x,sc, forget sc)) $ -}
>                    let (cl',Ind sc') = removeClaims claims (Ind sc) in
>                      if (nameOccurs x (forget sc'))
>                        then (cl', Ind (Bind x b (Sc sc')))
>                        else ((x,ty):cl', Ind sc')
>             | otherwise = ([], tm)

> refine _ _ _ _ _ = fail "Not focused on a hole"

        trace (show claims) $ fail "Unimplemented"

> getClaims :: TT Name -> [(Name, TT Name)]
> getClaims (Bind n (B Pi ty) (Sc sc)) = (n,ty):(getClaims sc)
> getClaims _ = []

> uniqifyClaims :: Name -> Env Name -> [(Name, TT Name)] -> [(Name, TT Name)]
> uniqifyClaims nspace env [] = []
> uniqifyClaims nspace env ((x,ty):xs) =
>     let newx = uniqify (mkns nspace x) (map fst env)
>         xs' = substClaim x (P newx) xs in
>         (newx, ty):(uniqifyClaims nspace ((newx, B Hole ty):env) xs')
>   where substClaim x newx [] = []
>         substClaim x newx ((n,ty):xs) 
>                        = (n,substName x newx (Sc ty)):
>                           (substClaim x newx xs)
>         mkns (UN a) (UN b) = UN (a++"_"++b)
>         mkns (MN (a,i)) (UN b) = MN (a++"_"++b, i)
>         mkns (MN (a,i)) (MN (b,j)) = MN (a++"_"++b, i)

> doClaims :: Name -> [((Name, TT Name), Maybe (TT Name))] -> Tactic
> doClaims h [] gam env tm = tacret $ tm
> doClaims h (((n,ty),Nothing):xs) gam env tm =
>     do (tm',_) <- runtacticEnv gam env h tm (claim n (forget ty))
>        doClaims h xs gam env tm'
> doClaims h (((n,ty),Just v):xs) gam env tm =
>     do (tm',_) <- runtacticEnv gam env h tm (claimsolved n (Ind v) (Ind ty))
>        doClaims h xs gam env tm'

Give up the current try

> regret :: Tactic
> regret _ _ (Ind (Bind x (B (Guess gv) ty) sc)) =
>     tacret $ Ind (Bind x (B Hole ty) sc)
> regret _ _ _ = fail "Can't regret something you haven't done"

Attempt to solve the current goal with the guess

> solve :: Tactic
> solve _ _ (Ind (Bind x (B (Guess gv) ty) sc)) 
>       | (pure gv) = tacret (Ind (Bind x (B (Let (finind gv)) ty) sc))
>       | otherwise = fail "I see a hole in your solution"
>    where finind t = case (finalise (Ind t)) of
>                        (Ind x) -> x
> solve _ _ _ = fail "Not a guess"

Substitute a let bound variable into a term

> cut :: Tactic
> cut _ env (Ind (Bind x (B (Let v) ty) sc)) =
>     tacret $ {- trace ("Cutting "++show v++" into "++show sc) $ -}
>            Ind (substName x (makePsEnv (map fst env) v) sc)
>   where 
> cut _ _ _ = fail "Not a let bound term"

Normalise the goal

> evalGoal :: Tactic
> evalGoal gam env (Ind (Bind x (B Hole ty) sc)) =
>    do let (Ind nty) = normaliseEnv (ptovenv env) gam (finalise (Ind ty))
>       tacret $ Ind (Bind x (B Hole nty) sc)
> evalGoal _ _ (Ind (Bind x _ _)) = fail $ "evalGoal: " ++ show x ++ " Not a hole"
> evalGoal _ _ _ = fail "evalGoal: Can't happen"

Do beta reductions (i.e., normalise the goal without expanding global names)

> betaReduce :: Tactic
> betaReduce gam env (Ind (Bind x (B Hole ty) sc)) =
>    do let (Ind nty) = normaliseEnv (ptovenv env) (Gam []) (finalise (Ind ty))
>       tacret $ Ind (Bind x (B Hole nty) sc)
> betaReduce _ _ (Ind (Bind x _ _)) = fail $ "betaReduce: " ++ show x ++ " Not a hole"
> betaReduce _ _ _ = fail "betaReduce: Not a binder, can't happen"

Normalise the goal, only expanding the given global name.

> reduceWith :: Name ->Tactic
> reduceWith fn gam env (Ind (Bind x (B Hole ty) sc)) =
>    do case glookup fn gam of
>           Nothing -> fail $ "Unknown name " ++ show fn
>           Just (v,t) -> do
>              let (Ind nty) = normaliseEnv (ptovenv env) 
>                                           (Gam [(fn,G v t defplicit)]) 
>                                           (finalise (Ind ty))
>              tacret $ Ind (Bind x (B Hole nty) sc)
> reduceWith _ _ _ (Ind (Bind x _ _)) = fail $ "reduceWith: " ++ show x ++ " Not a hole"
> reduceWith _ _ _ _ = fail "reduceWith: Not a binder, can't happen"

Do case analysis by the given elimination operator

> by :: Raw -> Tactic
> by rule gam env tm@(Ind (Bind x (B Hole ty) sc)) = 
>     do (Ind bv,Ind bt) <- check gam (ptovenv env) rule Nothing
>        let bvin = makePsEnv (map fst env) bv
>        let btin = makePsEnv (map fst env) bt
>        -- Take eliminator apart, find the motive and method names/types
>        (motive,methods) <- getBits btin
>        let motiveargs = getExpected (snd motive)
>        let eargs = getArgs bvin
>        let elimargs = drop (length eargs - length motiveargs) eargs
>        let tyuniq = uniqifyBinders (map fst motiveargs) ty
>        -- Construct the type of the motive Phi
>        let (Ind mtype) = finalise $ Ind $ bind Lambda motiveargs $ 
>                  Sc $ motiveType (zip (map fst motiveargs) elimargs) tyuniq
>        let mbinding = (B (Let mtype) (snd motive))
>        let claims = uniqifyClaims x env methods
>        (Ind mbody, []) 
>            <- doClaims x (zip claims (repeat Nothing)) gam (((fst motive),mbinding):env) tm
>        let mbind = Bind (fst motive) mbinding (Sc mbody)
>        let ruleapp = (forget (mkGuess claims (App bvin (P (fst motive)))))
>        (filled, _) <- runtacticEnv gam env x (Ind mbind)
>                         (fill ruleapp)
>        (tm', _) <- tidy gam env filled
>        --(tm'', _) <- runtacticEnv gam env (fst motive) tm' cut
>        return (tm', map HideGoal ((fst motive):(map fst claims)) ++
>                     map AddGoal (map fst (reverse claims)))
>   where
>     getBits (Bind mname (B Pi ty) (Sc sc)) 
>        | getReturnType ty == Star = do
>            meths <- getMeths sc
>            let names = map fst env
>            return ((mname,(uniqifyBinders names ty)), meths)
>     getBits _ = fail "What's my motivation?"
>     getMeths (Bind meth (B Pi ty) (Sc sc)) = do
>         rest <- getMeths sc
>         return ((meth,ty):rest)
>     getMeths _ = return []
>     motiveType [] ty = ty
>     motiveType ((marg,earg):xs) ty 
>         = let sc = (motiveType xs ty) in
>             --trace (show marg ++ " for " ++ show earg ++ " in " ++ show sc) $
>             substTerm earg (P marg) (Sc (motiveType xs ty))
>     mkGuess [] n = n
>     mkGuess ((x,_):xs) n = (mkGuess xs (App n (P x)))
> by _ _ _ _ = fail "Not focussed on a hole"

Do case analysis on the given term. Work out which elimination rule is
needed and the necessary indices, then run the 'by' tactic.

Either run the induction rule (if rec is true) or the case analysis rule
otherwise.

> casetac :: Bool -> Raw -> Tactic
> casetac rec scrutinee gam env tm@(Ind (Bind x (B Hole ty) sc)) = 
>     do (Ind bv,bt) <- check gam (ptovenv env) scrutinee Nothing
>        let (Ind btnorm) = (normaliseEnv (ptovenv env) gam bt)
>        let bvin = makePsEnv (map fst env) bv
>        let btin = makePsEnv (map fst env) btnorm
>        let indices = getArgs btin
>        let ty = getFun btin
>        runCaseTac rec ty (indices++[bvin]) gam env tm 
> casetac _ _ _ _ _ = fail "Not focussed on a hole"

> runCaseTac :: Bool -> TT Name -> [TT Name] -> Tactic
> runCaseTac rec (TyCon n _) args gam env tm =
>     case (lookupval n gam) of
>         (Just (TCon _ (Elims erule crule cons))) -> do
>             by (mkapp (Var (if rec then erule else crule))
>                                (map forget args)) gam env tm
>         (Just (TCon _ NoConstructorsYet)) -> 
>              fail $ (show n) ++ " is declared but not defined"
>         _ -> fail $ (show n) ++ " is not a type constructor"

> runCaseTac _ x indices gam env tm = 
>     fail $ (show x) ++ " is not a type constructor"

elimargs <- Get arguments to elimination operator
motiveargs <- Get expected arguments to motive
Remove args from elimargs so there are the right number to motiveargs
  (i.e. remove the ones which come from parameters)
motivetype <- goal subst[motiveargs for elimargs]
let motivename = lam motiveargs . motivetype
in [claim meths]


> uniqifyBinders env (Bind n (B Pi p) sc) 
>      | n `elem` env 
>          = let newname = uniqify n env in
>                Bind newname (B Pi p) 
>                         (Sc (substName n (P newname) sc))
>      | otherwise = Bind n (B Pi p) (fmap (uniqifyBinders env) sc)
> uniqifyBinders env x = x

Rename a binder

> rename :: Name -> Tactic
> rename n gam env (Ind (Bind x (B Hole rnin) sc))
>     = do renamed <- doRename n rnin
>          tacret $ Ind (Bind x (B Hole renamed) sc)
>   where doRename n (Bind x b sc)
>             = return (Bind n b (Sc (substName x (P n) sc)))
>         doRename _ _ = fail "Nothing to rename"
> rename _ _ _ (Ind (Bind x _ _)) = fail $ "rename: " ++ show x ++ " Not a hole"
> rename _ _ _ _ = fail "rename: Not a binder, can't happen"

Introduce a lambda or let

> intro :: Tactic
> intro gam env intm@(Ind (Bind x (B Hole tyin) (Sc p)))
>     | p == (P x) =
>         do let (Ind ty) = normaliseEnv (ptovenv env) (Gam []) (finalise (Ind tyin))
>            let ty' = makePsEnv (map fst env) ty
>            introsty (uniqify x (map fst env)) ty' (Sc p)
>     | otherwise = 
>            fail $ "Not an introduceable hole. Attack it first."
> intro _ _ _ = fail $ "Can't introduce here."

> introsty x (Bind y (B Pi s) (Sc t)) xscope =
>     tacret $ Ind (Bind y (B Lambda s) (Sc (Bind x (B Hole t) xscope)))
> introsty x (Bind y (B (Let v) s) (Sc t)) xscope =
>     tacret $ Ind (Bind y (B (Let v) s) (Sc (Bind x (B Hole t) xscope)))
> introsty x b xscope = fail $ "Nothing to introduce from " ++ show b

Tidy up a term to remove all holes which are not used.

> tidy :: Tactic
> tidy _ _ (Ind t) = tacret $ Ind $ tidy' t where
>    tidy' (Bind n (B Hole ty) (Sc sc))
>        | not $ n `elem` (getNames (Sc sc)) = tidy' sc
>    tidy' (Bind n (B (Guess _) ty) (Sc sc))
>        | not $ n `elem` (getNames (Sc sc)) = tidy' sc
>    tidy' (Bind n b (Sc sc)) =
>          Bind n (fmap tidy' b) (Sc (tidy' sc))
>    tidy' (App f a) = App (tidy' f) (tidy' a)
>    tidy' (Proj n i t) = Proj n i (tidy' t)
>    tidy' x = x

Replace a goal with an equivalent (convertible) goal.

> equiv :: Raw -> Tactic
> equiv goal gam env tm@(Ind (Bind x (B Hole ty) sc)) =
>     do (Ind goalv,Ind goalt) <- check gam (ptovenv env) goal Nothing
>        let goalvin = makePsEnv (map fst env) goalv
>        checkConvEnv env gam (Ind goalv) (finalise (Ind ty))
>                         "Not equivalent to the Goal"
>        tacret $ Ind (Bind x (B Hole goalvin) sc)
> equiv _ _ _ (Ind (Bind x _ _)) = fail $ "equiv: " ++ show x ++ " Not a hole"
> equiv _ _ _ _ = fail "equiv: Not a binder, can't happen"

> generalise :: Raw -> Tactic
> generalise expr gam env (Ind (Bind x (B Hole tyin) sc)) =
>     do (nv, nt) <- check gam (ptovenv env) expr Nothing
>        let (Ind ntyin) = normaliseEnv (ptovenv env) (Gam []) (finalise (Ind tyin))
>        let (Ind exprv) = normaliseEnv (ptovenv env) gam nv
>        let (Ind exprt) = normaliseEnv (ptovenv env) gam nt
>        let ty = makePsEnv (map fst env) ntyin
>        let exprvin = makePsEnv (map fst env) exprv
>        let exprtin = makePsEnv (map fst env) exprt
>        let newname = uniqify (UN "x") $
>                        (map fst env) ++ (getBoundNames (Sc ty))
>        let newtysc = unifySubstTerm gam exprvin (P newname) (Sc ty)
>        let newty = Bind newname (B Pi exprtin) (Sc newtysc)
>        let newsc = substName x (App (P x) exprvin) sc
>        tacret $ Ind (Bind x (B Hole newty) (Sc newsc))
> generalise _ _ _ (Ind (Bind x b sc)) = fail $ "generalise: " ++ show x ++ " Not a hole"
> generalise _ _ _ _ = fail "generalise: Can't happen"

Replace a term in the goal according to the given equality rule, and the
given equality type and replacement/symmetry lemmas.

Algorithm:
rule has type "eq X a b" (b is what we've got, a is what we want)
Create P = [n:X](ty[n/b])
claim p : ty[a/b]
try (repl _ _ _ rule P p)

Boolean flag (flip) is True if symmetry should be applied first.

> replace :: Raw -> Raw -> Raw -> Raw -> Bool -> Tactic
> replace eq repl sym rule flip gam env tm@(Ind (Bind x (B Hole ty) sc))
>         = do let userule = if flip
>                     then (mkapp sym [RInfer, RInfer, RInfer, rule])
>                     else rule
>              (Ind rulev, Ind rulet) <- check gam (ptovenv env) userule Nothing
>              (Ind eqv, Ind eqt) <- check gam (ptovenv env) eq Nothing
>              (Ind replv, Ind replt) <- check gam (ptovenv env) repl Nothing
>              (qty,a,b) <- getTypes rulet
>              let tP = (Bind nm (B Lambda qty) (Sc (substTerm b (P nm) (Sc ty))))
>              let p = substTerm b a (Sc ty)
>              (tm',_) <- doClaims x ([((claimname,p),Nothing)]) gam env tm
>              let repltm = mkapp repl (RInfer:RInfer:RInfer:userule:(forget tP):(Var claimname):[])
>              (filled, _) <- runtacticEnv gam env x tm' (fill repltm)
>              return (filled, [AddGoal claimname])
>    where psn = makePsEnv (map fst env)
>          nm = uniqify (UN "q") (map fst env)
>          claimname = mkns x (UN "q")
>          getTypes (App (App (App (App eq x) _) a) b) = return (x,a,b)
>          getTypes (App (App (App eq x) a) b) = return (x,a,b)
>          getTypes _ = fail "Rule is not of equality type"
>          mkns (UN a) (UN b) = UN (a++"_"++b)
> replace _ _ _ _ _ _ _ (Ind (Bind x b sc)) = fail $ "replace: " ++ show x ++ " Not a hole"
> replace _ _ _ _ _ _ _ _ = fail "replace: Not a binder, can't happen"

Create an axiom for the current goal (quantifying over all bound variables
in the goal, and [FIXME!] all variables they depend on) and use it to 
solve the goal.

> axiomatise :: Name -> [Name] -> Tactic
> axiomatise n helpers gam env tm@(Ind (Bind x (B Hole tyin) sc)) =
>     do let (Ind ty') = normaliseEnv (ptovenv env) (Gam []) (finalise (Ind tyin))
>        let ty = makePsEnv (map fst env) ty'
>        let fvs = reverse $ getUsedBoundVars env ((getNames (Sc ty))++helpers)
>        let axiom = bind Pi fvs (Sc ty)
>        return (Ind (Bind x 
>                     (B (Guess (appArgs (P n) (map (P . fst) fvs))) ty) sc),
>                    [AddAxiom n axiom])
>  where getUsedBoundVars [] ns = []
>        getUsedBoundVars ((n,b@(B _ ty)):bs) ns
>            | n `elem` ns = (n,ty):(getUsedBoundVars bs ns)
>            | otherwise = getUsedBoundVars bs ns
> axiomatise _ _ _ _ (Ind (Bind x b sc)) = fail $ "axiomatise: " ++ show x ++ " Not a hole"
> axiomatise _ _ _ _ _ = fail "axiomatise: Not a binder, can't happen"

Prepare to return a quoted value

> quote :: Tactic
> quote gam env tm@(Ind (Bind h (B Hole tyin) sc)) =
>     do let (Ind ty') = normaliseEnv (ptovenv env) (Gam []) (finalise (Ind tyin))
>        ty <- checkQuoted ty'
>        let qv = uniqify (mkns h (UN "qv")) $
>                        (map fst env) ++ (getBoundNames (Sc ty))
>        -- Fill hole with {'?qv:ty . qv}
>        let tm = (Bind qv (B Hole ty) (Sc (P qv)))
>        -- (tm',_) <- trace (show ty) $ runtacticEnv gam env h tm (claim qv (forget ty))
>        let filltm = Stage (Quote tm)
>        return (Ind (Bind h (B (Guess filltm) tyin) sc), [AddGoal qv])
>   where checkQuoted (Stage (Code t)) = return t
>         checkQuoted _ = fail "Not a code type"
>         mkns (UN a) (UN b) = UN (a++"_"++b)
> quote _ _ (Ind (Bind x b sc)) = fail $ "quote: " ++ show x ++ " Not a hole"
> quote _ _ _ = fail "quote: Not a binder, can't happen"

> ptovenv [] = []
> ptovenv ((x,b):xs) = (x,fmap finind b):(ptovenv xs)
>    where finind t = case finalise (Ind t) of
>                      (Ind t') -> t'
