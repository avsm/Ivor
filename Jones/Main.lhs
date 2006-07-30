> module Main where

Jones the Steam.
Simple program for starting up an interactive shell with Ivor library.

> import Ivor.TT
> import Ivor.Shell

> main :: IO ()
> main = do let shell = newShell emptyContext
>           ctxt <- runShell "> " shell
>           putStrLn "Finished"
