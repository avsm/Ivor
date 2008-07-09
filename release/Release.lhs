#!/usr/bin/env runhaskell

Build a release with documentation from the latest darcs version,
and upload it.

> module Main where

> import System.Environment
> import System.Exit
> import System.Directory
> import System.Process
> import Distribution.PackageDescription
> import Distribution.Package
> import Distribution.Verbosity
> import Data.Version

> repo = "http://www-fp.dcs.st-and.ac.uk/~eb/darcs/Ivor/"
> server = "eb@home-staff.dcs.st-and.ac.uk:public_html/Ivor/"

> main :: IO ()
> main = do args <- getArgs
>           dest <- parseArgs args
>           release dest

> parseArgs :: [String] -> IO String
> parseArgs (dest:[]) = return dest
> parseArgs [] = return server
> parseArgs _ = do putStrLn "Usage:\n\trelease [upload_location]"
>                  exitWith (ExitFailure 1)

> release :: String -> IO ()
> release dest = do
>     shell $ "darcs get --partial " ++ repo
>     gpkg <- readPackageDescription verbose "Ivor/ivor.cabal"
>     let pkg = flattenPackageDescription gpkg
>     let pkgver = pkgVersion (package pkg)
>     let ver = getVer (versionBranch pkgver)
>     putStrLn $ "Making a release of Ivor version " ++ ver
>     let rootname = "ivor-"++ver
>     shell $ "rm -rf Ivor/_darcs"
>     shell $ "rm -rf Ivor/release"
>     shell $ "mv Ivor " ++ rootname
>     shell $ "tar zcvf "++rootname++".tgz "++rootname++"/"
>     setCurrentDirectory rootname
>     shell $ "make jones"
>     shell $ "strip Jones/jones"
>     shell $ "runhaskell Setup.lhs haddock"
>     setCurrentDirectory ".."
>     shell $ "gpg -b " ++ rootname ++ ".tgz"
>     shell $ "gpg -b " ++ rootname ++ "/Jones/jones"
>     shell $ "scp "++rootname++".tgz " ++ rootname ++"/Jones/jones " 
>                   ++rootname++".tgz.sig " ++ rootname ++ "/Jones/jones.sig " ++ dest
>     shell $ "scp "++rootname++"/dist/doc/html/* "++dest++"doc"
>     shell $ "rm -rf " ++ rootname

> getVer [] = "none"
> getVer (major:[]) = show major
> getVer (major:minor:[]) = show major ++ "." ++ show minor
> getVer (major:minor:pl:_) = show major ++ "." ++ show minor ++ "." ++ show pl

> shell :: String -> IO ()
> shell cmd = do p <- runCommand cmd
>                waitForProcess p
>                return ()
