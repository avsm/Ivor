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

> -- | Load the given plugin file (which should be a full path to a .o or
> -- .hs file) and update the Context. If it is a .hs file, it will be
> -- compiled if necessary.
> -- Plugins must contain the symbol
> -- @plugin_context :: Monad m => Context -> m Context
> -- which updates the context. It may optionally contain symbols
> -- @plugin_parser :: Parser ViewTerm
> -- which adds new parsing rules,
> -- @plugin_commands :: [(String, String -> COntext -> IO (String, Context))]
> -- which adds new user defined commands.
> -- Returns the new context and the extra parsing rules/commands, if any.

> load :: FilePath -> Context -> 
>           IO (Context, 
>               Maybe (Parser ViewTerm),
>               Maybe [(String, String -> Context -> IO (String, Context))])
> load fn ctxt = do 
>          objIn <- compilePlugin fn
>          obj <- case objIn of
>                    Left errs -> fail errs
>                    Right ok -> return ok
>          contextMod <- Plugins.load_ obj [] "plugin_context"
>          -- mv <- Plugins.load fn [] ["/Users/edwin/.ghc/i386-darwin-6.6.1/package.conf"] "initialise"
>          (mod, contextFn) <- case contextMod of
>                  LoadFailure msg -> fail $ "Plugin loading failed: " ++
>                                              show msg
>                  LoadSuccess mod v -> return (mod, v)
>          parserMod <- Plugins.reload mod "plugin_parser"
>          parserules <- case parserMod of
>                  LoadFailure msg -> return Nothing
>                  LoadSuccess _ v -> return $ Just v
>          cmdMod <- Plugins.reload mod "plugin_commands"
>          cmds <- case cmdMod of
>                  LoadFailure msg -> return Nothing
>                  LoadSuccess _ v -> return $ Just v
>          ctxt' <- case contextFn ctxt of
>                      Just x -> return x
>                      Nothing -> fail "Error in running plugin_context"
>          return $ (ctxt', parserules, cmds)

Make a .o from a .hs, so that we can load Haskell source as well as object
files

> compilePlugin :: FilePath -> IO (Either String FilePath)
> compilePlugin hs 
>     | isExt ".hs" hs || isExt ".lhs" hs =
>         do status <- make hs []
>            case status of
>               MakeSuccess c out -> return $ Right out
>               MakeFailure errs -> return $ Left (concat (map (++"\n") errs))
>     | isExt ".o" hs = return $ Right hs
>     | elem '.' hs = return (Left $ "unrecognised file type " ++ hs)
>     | otherwise = compilePlugin (hs++".o")
>   where isExt ext fn = case span (/='.') fn of
>                           (file, e) -> ext == e