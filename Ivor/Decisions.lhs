> {-# OPTIONS_GHC -fglasgow-exts #-}

> -- | 
> -- Module      : Ivor.Decisions
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> -- 
> -- Some decision procedures

> module Ivor.Decisions(auto,split,left,right,useCon) where

> import Ivor.TT

> -- | Tries to solve a simple goal automatically by trying each of these 
> --   in turn:
> --  * Looking for an assumption ('trivial')
> --  * 'intros' everything then solve by 'auto'
> --  * Splitting the goal, then solving each subgoal by 'auto'
> --  * If the goal is of a type with more than one constructor, try 'auto'
> --    on each constructor in turn.
> auto :: Int -- ^ Search depth
>         -> Tactic
> auto _ = fail "auto undefined"

> -- | Split a goal into subgoals. Type of goal must be a one constructor
> -- family, with constructor @c@, then proceeds by 'refine' @c@.
> split :: Tactic
> split  = useCon 1 0

> -- | Split a goal into subgoals. Type of goal must be a two constructor
> -- family, with constructors @l@ and @r@, then proceeds by 'refine' @l@.
> left :: Tactic
> left = useCon 2 0

> -- | Split a goal into subgoals. Type of goal must be a two constructor
> -- family, with constructors @l@ and @r@, then proceeds by 'refine' @r@.
> right :: Tactic
> right = useCon 2 1

Get the goal, look at the type. Refine by the constructor of that type -
check that there is the right number (num).

> -- | Solve the goal by applying a numbered constructor
> useCon :: Int -- ^ Ensure at least this number of constructors (0 for no constraint)
>           -> Int -- ^ Use this constructor (0 based, order of definition)
>           -> Tactic
> useCon num use g ctxt = do
>     goal <- goalData ctxt False g
>     let ty = getApp (view (goalType goal))
>     case ty of
>       (Name _ n) -> do cons <- getConstructors ctxt n
>                        splitnCon cons g ctxt
>       _ -> fail "Not a type constructor"
>    where splitnCon cs | length cs >= num || num == 0
>              = refine (Name DataCon (cs!!use))
>          splitnCon _ = fail $ "Not a " ++ show num ++ " constructor family"

