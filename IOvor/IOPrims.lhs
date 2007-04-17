> module IOPrims where

> import System.IO
> import System.IO.Unsafe
> import Data.Typeable
> import Debug.Trace

> import Ivor.Primitives
> import Ivor.TT

IO primitives; adds 'RealWorld' and 'Handle'

RealWorld is a dummy type representing the world state, Handle (from 
System.IO) gives file handles.

> data RealWorld = RW ()
>    deriving Eq

> instance Show RealWorld where
>     show _ = "<<World>>"

> rwName = name "RealWorld"

> instance Typeable RealWorld where
>     typeOf (RW ()) = mkTyConApp (mkTyCon "RW") []

> instance ViewConst RealWorld where
>     typeof x = rwName

> instance ViewConst Handle where
>     typeof x = (name "Handle")

> addIOPrimTypes :: Monad m => Context -> m Context
> addIOPrimTypes c = do c <- addPrimitives c
>                       c <- addPrimitive c rwName
>                       c <- addPrimitive c (name "Handle")
>                       c <- addExternalFn c (name "initWorld") 1 initWorld
>                              "True -> RealWorld"
>                       return c

> addIOPrimFns :: Monad m => Context -> m Context
> addIOPrimFns c = do c <- addBinFn c (name "putStr") doPutStr
>                             "String -> (IO True)"
>                     c <- addPrimFn c (name "getLine") doGetLine
>                             "(IO String)"
>                     return c

Make an instance of IOResult from the result of an IO action and a 
value

> mkIO :: () -> ViewTerm -> ViewTerm
> mkIO t v = case (t,v) of -- make sure they get evaluated
>               (tr,val) -> apply (Name DataCon (name "ioResult"))
>                             [Placeholder, Constant (RW tr), val]

> trueVal = Name DataCon (name "II")

> {-# NOINLINE doPutStr #-}
> doPutStr :: String -> RealWorld -> ViewTerm
> doPutStr str w = mkIO () trueVal -- (unsafePerformIO (putStr str)) trueVal

> {-# NOINLINE doGetLine #-}
> doGetLine :: RealWorld -> ViewTerm
> doGetLine w = mkIO () (Constant "foo") -- (unsafePerformIO getLine))

Needs a dummy argument so that evaluator doesn't loop

> initWorld :: [ViewTerm] -> ViewTerm
> initWorld [_] = Constant (RW ())
