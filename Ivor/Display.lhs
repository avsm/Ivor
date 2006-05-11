> {-# OPTIONS_GHC -fglasgow-exts #-}  {- -*-literate-haskell-*- -}

Functions for displaying proof state "helpfully".

> module Ivor.Display where

> import Ivor.Tactics
> import Ivor.TTCore
> import Ivor.Typecheck
> import Ivor.Nobby

> displayHoleContext :: Gamma Name -> Name -> Indexed Name -> String
> displayHoleContext gam h tm = 
>     case (findhole gam (Just h) tm displayHole) of
>             Just x -> x
>             Nothing -> ""

> displayHole :: Gamma Name -> Env Name -> Indexed Name -> String
> displayHole gam hs tm = dh hs ++ 
>                         "\n=======================================\n" ++
>                         show (normaliseEnv hs (Gam []) tm) ++ "\n"
>    where dh [] = ""
>          dh ((n,B _ ty):xs) = 
>              dh xs ++ (show n)++" : "++show ty++"\n"

