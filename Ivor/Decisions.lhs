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

> module Ivor.Decisions(auto,split) where

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

Get the goal, look at the type. Refine by the constructor of that type -
check that there is only one

> split g ctxt = do
>     goal <- goalData ctxt False g
>     let ty = getApp (view (goalType goal))
>     case ty of
>       (Name _ n) -> do cons <- getConstructors ctxt n
>                        splitOneCon cons g ctxt
>       _ -> fail "Not a type constructor"
>    where splitOneCon [c] = refine (Name DataCon c)
>          splitOneCon _ = fail "Not a single constructor family"
