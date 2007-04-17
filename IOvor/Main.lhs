> module Main where

Jones the Steam, with IO primitives.
Simple program for starting up an interactive shell with Ivor library.

> import Ivor.TT
> import Ivor.Shell
> import Ivor.Primitives

> import IOPrims

> main :: IO ()
> main = do let shell = addModulePath (newShell emptyContext) 
>                          (prefix ++ "/lib/ivor")
>           shell <- importFile "basics.tt" shell
>           primCtxt <- addIOPrimTypes (getContext shell)
>           let shell' = addModulePath (newShell primCtxt) 
>                          (prefix ++ "/lib/ivor")
>           shell' <- importFile "iobasics.tt" shell'
>           primFnCtxt <- addIOPrimFns (getContext shell')
>           -- It is horrible to have to do this every time. Fix the API!
>           let shell'' = addModulePath (newShell primFnCtxt) 
>                          (prefix ++ "/lib/ivor")
>           ctxt <- runShell "> " (extendParser shell'' parsePrimitives)
>           putStrLn "Finished"
