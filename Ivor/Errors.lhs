> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Ivor.Errors where

> import Ivor.TTCore
> import Control.Monad.Error

> data IError = ICantUnify (Indexed Name) (Indexed Name)
>             | INotConvertible (Indexed Name) (Indexed Name)
>             | IMessage String
>             | IUnbound (Indexed Name) (Indexed Name) (Indexed Name) (Indexed Name) [Name]
>             | INoSuchVar Name
>             | ICantInfer Name (Indexed Name)
>             | IContext String IError
>   deriving (Show, Eq)

> instance Error IError where
>     noMsg = IMessage "Ivor Error"
>     strMsg s = IMessage s

> type IvorM = Either IError

> ifail = Left

Generic error checking can go here:

Check that all the names are real rather than implicit and inferred

> checkRealNames :: [Name] -> Indexed Name -> IvorM ()
> checkRealNames [] tm = return ()
> checkRealNames (nm@(MN ("INFER", n)): ns) tm = ifail (ICantInfer nm tm)
> checkRealNames (_:ns) tm = checkRealNames ns tm
