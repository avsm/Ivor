> {-# OPTIONS_GHC -fglasgow-exts #-}

> -- | 
> -- Module      : Ivor.Shell
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> -- 
> -- Shell interface to theorem prover

> module Ivor.ShellState(ShellState(..)) where

> import Ivor.TT as TT
> import Text.ParserCombinators.Parsec

> data ShellState = Shell {
>                          repldata :: Maybe (String, String, String),
>                          prompt :: String,
>                          finished :: Bool,
>                          context :: !Context,
>                          -- | Get reply from last shell command
>                          response :: String,
>                          usertactics :: [(String, String -> Goal -> Context -> TTM Context)],
>                          usercommands :: [(String, String -> Context -> IO (String, Context))],
>                          imported :: [String],
>                          extensions :: Maybe (Parser ViewTerm),
>                          -- search path for modules to load
>                          modulePath :: [FilePath]
>                          }


