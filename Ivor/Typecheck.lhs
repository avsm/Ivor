> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Typecheck(module Ivor.Typecheck, Gamma) where

> import Ivor.TTCore
> import Ivor.Gadgets
> import Ivor.Nobby
> import Ivor.Unify
> import Ivor.Constant

> import Control.Monad.State
> import Debug.Trace

Conversion in the presence of staging is a bit more than simply syntactic
equality on values, since it is possible values contain quoted code which
code be run later. So we say {'x} =~ {'y] iff x =~ y. Otherwise it's 
syntactic.

> convert :: Gamma Name -> Indexed Name -> Indexed Name -> Bool
> convert g x y = convertEnv [] g x y

> convertEnv env g x y 
>     = (convNormaliseEnv env g x) == (convNormaliseEnv env g y)
>   -- conv (Stage (Quote x)) (Stage (Quote y)) = convertEnv env g x y
>   -- need to actually reduce inside quotes to do conversion check

 convert g x y = trace ((show (normalise g x)) ++ " & " ++ (show (normalise g y))) $ (normalise g x)==(normalise g y)

> checkConv :: Monad m => Gamma Name -> Indexed Name -> Indexed Name -> 
>              String -> m ()
> checkConv g x y err = if convert g x y then return ()
>	                 else fail err

> checkConvEnv :: Monad m => Env Name -> Gamma Name -> 
>                 Indexed Name -> Indexed Name -> 
>              String -> m ()
> checkConvEnv env g x y err = if convertEnv env g x y then return ()
>                              else fail err


Top level typechecking function - takes a context and a raw term,
returning a pair of a term and its type

> typecheck :: Monad m => Gamma Name -> Raw -> m (Indexed Name,Indexed Name)
> typecheck gamma term = do t <- check gamma [] term Nothing
>			    {-trace (show t) $-}
>                           return t

> tcClaim :: Monad m => Gamma Name -> Raw -> m (Indexed Name,Indexed Name)
> tcClaim gamma term = do (Ind t, Ind v) <- check gamma [] term Nothing
>			    {-trace (show t) $-}
>                         return (Ind (makePs t), Ind (makePs v))

Check takes a global context, a local context, the term to check and
its expected type, if known, and returns a pair of a term and its
type.

> type CheckState = (Int, [(Indexed Name, Indexed Name)])
> type Level = Int

> check :: Monad m => Gamma Name -> Env Name -> Raw -> Maybe (Indexed Name) -> 
>          m (Indexed Name, Indexed Name)
> check = lvlcheck 0

> lvlcheck :: Monad m => Level -> Gamma Name -> Env Name -> Raw -> 
>             Maybe (Indexed Name) -> 
>             m (Indexed Name, Indexed Name)
> lvlcheck lvl gamma env tm exp 
>     = do tm' <- evalStateT (tcfixup env lvl tm exp) (0, []) 
>          return tm'
>  where

Do the typechecking, then unify all the inferred terms.

>  tcfixup env lvl t exp = do
>     tm <- tc env lvl t exp
>     (next, errs) <- get
>     tm' <- fixup errs tm
>     put (next, [])
>     return tm'

tc has state threaded through -- state is a tuple of the next name to
generate, the stage we're at, and a list of conversion errors (which
will later be unified).  Needs an explicit type to help out ghc's
typechecker...

>  tc :: Monad m => Env Name -> Level -> Raw -> Maybe (Indexed Name) ->
>                   StateT CheckState m (Indexed Name, Indexed Name)
>  tc env lvl (Var n) exp =
>        mkTT (lookupi n env 0) (glookup n gamma)
>    where mkTT (Just (i, B _ t)) _ = return (Ind (P n), Ind t)
>          mkTT Nothing (Just ((Fun _ _),t)) = return (Ind (P n), t)
>          mkTT Nothing (Just ((Partial _ _),t)) = return (Ind (P n), t)
>          mkTT Nothing (Just (Unreducible,t)) = return (Ind (P n), t)
>          mkTT Nothing (Just (Undefined,t)) = return (Ind (P n), t)
>          mkTT Nothing (Just ((ElimRule _),t)) = return (Ind (Elim n), t)
>          mkTT Nothing (Just ((PrimOp _),t)) = return (Ind (P n), t)
>          mkTT Nothing (Just ((DCon tag i),t)) = return (Ind (Con tag n i), t)
>          mkTT Nothing (Just ((TCon i _),t)) = return (Ind (TyCon n i), t)
>          mkTT Nothing Nothing = fail $ "No such name as " ++ show n

>          lookupi x [] _ = Nothing
>          lookupi x ((n,t):xs) i | x == n = Just (i,t)
>          lookupi x (_:xs) i = lookupi x xs (i+1)

>  tc env lvl (RApp f a) exp = do
>     (Ind fv, Ind ft) <- tcfixup env lvl f Nothing
>     let fnfng = normaliseEnv env (Gam []) (Ind ft)
>     let fnf = normaliseEnv env gamma (Ind ft)
>     case (fnfng,fnf) of
>       ((Ind (Bind _ (B Pi s) (Sc t))),_) -> do
>          (Ind av,Ind at) <- tcfixup env lvl a (Just (Ind s))
>          checkConvSt env gamma (Ind at) (Ind s) $ "Type error: " ++ show a ++ " : " ++ show at ++ ", expected type "++show s -- ++" "++show env
>          let tt = (Bind (MN ("x",0)) (B (Let av) at) (Sc t))
>          return (Ind (App fv av), (normaliseEnv env (Gam []) (Ind tt)))
>       (_, (Ind (Bind _ (B Pi s) (Sc t)))) -> do
>          (Ind av,Ind at) <- tcfixup env lvl a (Just (Ind s))
>          checkConvSt env gamma (Ind at) (Ind s) $ "Type error: " ++ show a ++ " : " ++ show at ++ ", expected type "++show s -- ++" "++show env
>          let tt = (Bind (MN ("x",0)) (B (Let av) at) (Sc t))
>          return (Ind (App fv av), (normaliseEnv env gamma (Ind tt)))
>       _ -> fail $ "Cannot apply a non function type " ++ show ft ++ " to " ++ show a
>  tc env lvl (RConst x) _ = tcConst x
>  tc env lvl RStar _ = return (Ind Star, Ind Star)
>  tc env lvl (RBind n b sc) exp = do
>     gb <- checkbinder gamma env lvl n b
>     let scexp = case exp of
>          Nothing -> Nothing
>          (Just (Ind (Bind sn sb (Sc st)))) -> Just $
>             normaliseEnv ((sn,sb):env) gamma (Ind st)
>     (Ind scv, Ind sct) <- tcfixup ((n,gb):env) lvl sc scexp
>     --discharge gamma n gb (Sc scv) (Sc sct)
>     discharge gamma n gb (pToV n scv) (pToV n sct)
>  tc env lvl l@(RLabel t comp) _ = do
>     (Ind tv, Ind tt) <- tcfixup env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>       (Ind Star) -> do compv <- checkComp env lvl comp
>                        return (Ind (Label tv compv), Ind Star)
>       _ -> fail $ "Type of label " ++ show l ++ " must be *"
>  tc env lvl (RCall comp t) _ = do
>     compv <- checkComp env lvl comp
>     (Ind tv, Ind tt) <- tcfixup env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>       (Ind (Label t comp)) -> return (Ind (Call compv tv), Ind t)
>       _ -> fail $ "Type of call must be a label"
>  tc env lvl (RReturn t) (Just exp) = do
>     let expnf = normaliseEnv env gamma exp
>     case expnf of
>       (Ind (Label lt comp)) -> do
>          (Ind tv, Ind tt) <- tcfixup env lvl t (Just (Ind lt))
>          checkConvSt env gamma (Ind lt) (Ind tt) $ 
>             "Type error: " ++ show tt ++", expected type " ++ show lt
>          return (Ind (Return tv), Ind (Label tt comp))
>       _ -> fail $ "return " ++ show t++ " should give a label, got " ++ show expnf
>  tc env lvl (RReturn t) Nothing = fail $ "Need to know the type to return for "++show t
>  tc env lvl (RStage s) exp = do
>          (Ind sv, Ind st) <- tcStage env lvl s exp
>          return (Ind sv, Ind st)
>  tc env lvl RInfer (Just exp) = do 
>                       (next,errs) <- get
>                       put (next+1, errs)
>                       return (Ind (P (MN ("INFER",next))), exp)
>  tc env lvl RInfer Nothing = fail "Can't infer a term for placeholder"

>  tcStage env lvl (RQuote t) _ = do
>     (Ind tv, Ind tt) <- tc env (lvl+1) t Nothing
>     return (Ind (Stage (Quote tv)), Ind (Stage (Code tt)))
>  tcStage env lvl (RCode t) _ = do
>     (Ind tv, Ind tt) <- tc env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>       (Ind Star) -> return (Ind (Stage (Code tv)), Ind Star)
>       _ -> fail $ "Type of code " ++ show t ++ " must be *"
>  tcStage env lvl (REval t) _ = do
>     -- when (lvl/=0) $ fail $ "Can't eval at level " ++ show lvl
>     (Ind tv, Ind tt) <- tc env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>        (Ind (Stage (Code tcode))) -> 
>            return (Ind (Stage (Eval tv tt)), Ind tcode)
>        _ -> fail $ "Can't eval a non-quoted term (type " ++ show ttnf ++ ")"
>  tcStage env lvl (REscape t) _ = do
>     -- when (lvl==0) $ fail $ "Can't escape at level " ++ show lvl
>     (Ind tv, Ind tt) <- tc env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>        (Ind (Stage (Code tcode))) -> 
>            return (Ind (Stage (Escape tv tt)), Ind tcode)
>        _ -> fail "Can't escape a non-quoted term"

>  checkComp env lvl (RComp n ts) = do
>     tsc <- mapM (\ t -> tcfixup env lvl t Nothing) ts
>     return (Comp n (map ( \ (Ind v, Ind t) -> v) tsc))

>  checkConvSt env g x y err = if convertEnv env g x y then return ()
>                              else do (next,err) <- get
>                                      put (next,(x,y):err)
>                                      return ()

Insert inferred values into the term

>  fixup [] tm = return tm
>  fixup ((x,y):xs) (Ind tm, Ind ty) = do 
>      uns <- case unify gamma y x of
>                 Success x -> return x
>                 Failure err -> fail $ "Can't convert "++show x++" and "++show y ++ " ("++show err++")"
>      let tm' = fixupNames uns tm
>      let ty' = fixupNames uns ty
>      fixup xs (Ind tm', Ind ty')

>  fixupNames [] tm = tm
>  fixupNames ((x,ty):xs) tm = fixupNames xs $ substName x ty (Sc tm)

>  tcConst :: (Monad m, Constant c) => c -> m (Indexed Name, Indexed Name)
>  tcConst c = return (Ind (Const c), Ind (constType c))

 tcConst Star = return (Ind (Const Star), Ind (Const Star)) --- *:* is a bit dodgy...

  checkbinder :: Monad m => Gamma Name -> Env Name -> Level ->
	          Name -> Binder Raw -> m (Binder (TT Name))

>  checkbinder gamma env lvl n (B Lambda t) = do
>     (Ind tv,Ind tt) <- tcfixup env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>       (Ind Star) -> return (B Lambda tv)
>       _ -> fail $ "The type of the binder " ++ show n ++ " must be *"
>  checkbinder gamma env lvl n (B Pi t) = do
>     (Ind tv,Ind tt) <- tcfixup env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>       (Ind Star) -> return (B Pi tv)
>       _ -> fail $ "The type of the binder " ++ show n ++ " must be *"
>  checkbinder gamma env lvl n (B (Let v) t) = do
>     (Ind tv,Ind tt) <- tcfixup env lvl t Nothing
>     (Ind vv,Ind vt) <- tcfixup env lvl v (Just (Ind tv))
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     checkConvEnv env gamma (Ind vt) (Ind tv) $ 
>        show vt ++ " and " ++ show tv ++ " are not convertible\n" ++ 
>             dbg (normaliseEnv env gamma (Ind vt)) ++ "\n" ++
>             dbg (normaliseEnv env gamma (Ind tv)) ++ "\n"
>     case ttnf of
>       (Ind Star) -> return (B (Let vv) tv)
>       _ -> fail $ "The type of the binder " ++ show n ++ " must be *"
>    where dbg (Ind t) = debugTT t

>  checkbinder gamma env lvl n (B Hole t) = do
>     (Ind tv,Ind tt) <- tcfixup env lvl t Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     case ttnf of
>       (Ind Star) -> return (B Hole tv)
>       _ -> fail $ "The type of the binder " ++ show n ++ " must be *"
>  checkbinder gamma env lvl n (B (Guess v) t) = do
>     (Ind tv,Ind tt) <- tcfixup env lvl t Nothing
>     (Ind vv,Ind vt) <- tcfixup env lvl v Nothing
>     let ttnf = normaliseEnv env gamma (Ind tt)
>     checkConvEnv env gamma (Ind vt) (Ind tv) $ 
>        show vt ++ " and " ++ show tv ++ " are not convertible"
>     case ttnf of
>       (Ind Star) -> return (B (Guess vv) tv)
>       _ -> fail $ "The type of the binder " ++ show n ++ " must be *"

> discharge :: Monad m =>
>              Gamma Name -> Name -> Binder (TT Name) -> 
>	       (Scope (TT Name)) -> (Scope (TT Name)) ->
>	       m (Indexed Name, Indexed Name)
> discharge gamma n (B Lambda t) scv sct = do
>    let lt = Bind n (B Pi t) sct
>    let lv = Bind n (B Lambda t) scv
>    return (Ind lv,Ind lt)
> discharge gamma n (B Pi t) scv (Sc sct) = do
>    checkConv gamma (Ind Star) (Ind sct) $ 
>       "The scope of a Pi binding must be a type"
>    let lt = Star
>    let lv = Bind n (B Pi t) scv
>    return (Ind lv,Ind lt)
> discharge gamma n (B (Let v) t) scv sct = do
>    let lt = Bind n (B (Let v) t) sct
>    let lv = Bind n (B (Let v) t) scv
>    return (Ind lv,Ind lt)
> discharge gamma n (B Hole t) scv (Sc sct) = do
>    let lt = sct -- already checked sct and t are convertible
>    let lv = Bind n (B Hole t) scv
>    -- A hole can't appear in the type of its scope, however.
>    checkNotHoley 0 sct
>    return (Ind lv,Ind lt)
> discharge gamma n (B (Guess v) t) scv (Sc sct) = do
>    let lt = sct -- already checked sct and t are convertible
>    let lv = Bind n (B (Guess v) t) scv
>    -- A hole can't appear in the type of its scope, however.
>    checkNotHoley 0 sct
>    return (Ind lv,Ind lt)

> checkNotHoley :: Monad m => Int -> TT n -> m ()
> checkNotHoley i (V v) | v == i = fail "You can't put a hole where a hole don't belong."
> checkNotHoley i (App f a) = do checkNotHoley i f
>                                checkNotHoley i a
> checkNotHoley i (Bind _ _ (Sc s)) = checkNotHoley (i+1) s
> checkNotHoley i (Proj _ _ t) = checkNotHoley i t
> checkNotHoley _ _ = return ()

> pToV :: Eq n => n -> (TT n) -> (Scope (TT n))
> pToV = pToV2 0

> pToV2 v p (P n) | p==n = Sc (V v)
>                 | otherwise = Sc (P n)
> pToV2 v p (V w) = Sc (V w)
> pToV2 v p (Con t n i) = Sc (Con t n i)
> pToV2 v p (TyCon n i) = Sc (TyCon n i)
> pToV2 v p (Elim n) = Sc (Elim n)
> pToV2 v p (Bind n b (Sc sc)) = Sc (Bind n (fmap (getSc.(pToV2 v p)) b)
>                                    (pToV2 (v+1) p sc))
>				where getSc (Sc a) = a
> pToV2 v p (App f a) = Sc $ App (getSc (pToV2 v p f))
>                               (getSc (pToV2 v p a))
>				where getSc (Sc a) = a
> pToV2 v p (Label t (Comp n ts)) = Sc $ Label (getSc (pToV2 v p t))
>                                         (Comp n (map (getSc.(pToV2 v p)) ts))
> pToV2 v p (Call (Comp n ts) t) = Sc $ Call 
>                                        (Comp n (map (getSc.(pToV2 v p)) ts))
>                                        (getSc (pToV2 v p t))
> pToV2 v p (Return t) = Sc $ Return (getSc (pToV2 v p t))
> pToV2 v p (Proj n i t) = Sc $ Proj n i (getSc (pToV2 v p t))
>				where getSc (Sc a) = a
> pToV2 v p (Stage t) = Sc $ Stage (sLift (getSc.(pToV2 v p)) t)
> pToV2 v p (Const x) = Sc (Const x)
> pToV2 v p Star = Sc Star

> checkR g t = (typecheck g t):: (Result (Indexed Name, Indexed Name)) 

If we're paranoid - recheck a supposedly well-typed term. Might want to
do this after finishing a proof.

> verify :: Monad m => Gamma Name -> Indexed Name -> m ()
> verify gam tm = do (_,_) <- typecheck gam (forget tm)
>                    return ()