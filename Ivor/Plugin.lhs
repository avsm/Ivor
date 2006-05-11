> {-# OPTIONS_GHC -fglasgow-exts #-}

> -- | 
> -- Module      : Ivor.Plugin
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : portable
> -- 
> -- Plugin loader

> module Ivor.Plugin(Ivor.Plugin.load) where

> import Ivor.TT
> import System.Plugins as Plugins
> import Text.ParserCombinators.Parsec

> -- | Load the given plugin file (which should be a full path to a .o file)
> -- and update the Context.
> -- Plugins must contain the symbol
> -- @initialise :: Context -> (Context, Maybe (Parser ViewTerm))@
> -- which updates the context and returns any parser extensions.

> load :: FilePath -> Context -> IO (Context, Maybe (Parser ViewTerm))
> load fn ctxt = do 
>          mv <- Plugins.load fn [] [] "initialise" -- "/home/eb/.ghc/i386-linux-6.4.1/package.conf"] "initialise"
>          initialise <- case mv of
>                  LoadFailure msg -> fail $ "Plugin loading failed: " ++ (show msg)
>                  LoadSuccess _ v -> return v
>          return $ initialise ctxt
