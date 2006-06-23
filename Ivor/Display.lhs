> {-# OPTIONS_GHC -fglasgow-exts #-}  {- -*-literate-haskell-*- -}

Functions for displaying proof state "helpfully".

> module Ivor.Display where

> import Ivor.Tactics
> import Ivor.TTCore
> import Ivor.Typecheck
> import Ivor.Nobby

> displayHoleContext :: Gamma Name -> [Name] -> Name -> Indexed Name -> String
> displayHoleContext gam hidden h tm = 
>     case (findhole gam (Just h) tm (displayHole hidden)) of
>             Just x -> x
>             Nothing -> ""

> displayHole :: [Name] -> Gamma Name -> Env Name -> Indexed Name -> String
> displayHole hidden gam hs tm = dh hs ++ 
>                         "\n=======================================\n" ++
>                         show (normaliseEnv hs (Gam []) tm) ++ "\n"
>    where dh [] = ""
>          dh ((n,B _ ty):xs) 
>              | n `elem` hidden = dh xs
>              | otherwise = dh xs ++ (show n)++" : "++show ty++"\n"

