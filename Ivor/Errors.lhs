> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Errors where

> import Ivor.TTCore
> import Control.Monad.Error

> data IError = ICantUnify (Indexed Name) (Indexed Name)
>             | IMessage String
>   deriving Show

> instance Error IError where
>     noMsg = IMessage "Ivor Error"
>     strMsg s = IMessage s

> type IvorM = Either IError

> ifail = Left
