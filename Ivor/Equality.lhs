> {-# OPTIONS_GHC -fglasgow-exts #-}

> -- | 
> -- Module      : Ivor.Equality
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> -- 
> -- Tactics for Heterogeneous Equality (injectivity, disjointness, etc)

> module Ivor.Equality where

> import Ivor.TTCore as TTCore
> import Ivor.TT
> import Ivor.TermParser
> import Ivor.State
> import Ivor.Gadgets
> import Ivor.Nobby

