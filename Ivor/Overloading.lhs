Facilities for handling overloading. This is currently a bodge - terms
contain 'ROpts' which are variables which could be one of several things.
We convert such terms to a list of terms which contain all the possible 
combinations of 'Var', typecheck them all, and if only one succeeds, that's
the right overloading. If more than one succeeds, there is an ambiguous name.

> module Ivor.Overloading where

> import Ivor.TTCore

> getTerms :: Raw -> [Raw]
> getTerms (Var n) = return $ Var n
> getTerms (ROpts ns) = do n <- ns
>                          return $ Var n
> getTerms (RApp f a) = do f' <- getTerms f
>                          a' <- getTerms a
>                          return $ RApp f' a'
> getTerms (RBind n (B b t) sc)
>                     = do b' <- gtb b
>                          t' <- getTerms t
>                          sc' <- getTerms sc
>                          return $ RBind n (B b' t') sc'
>    where gtb Lambda = return Lambda
>          gtb Pi = return Pi
>          gtb (Let t) = do t' <- getTerms t
>                           return $ Let t'
>          gtb Hole = return Hole
>          gtb (Guess t) = do t' <- getTerms t
>                             return $ Guess t'
>          gtb (Pattern t) = do t' <- getTerms t
>                               return $ Guess t'
>          gtb MatchAny = return MatchAny
> getTerms (RFileLoc f l t) = do t' <- getTerms t
>                                return (RFileLoc f l t')
> getTerms t = return t
