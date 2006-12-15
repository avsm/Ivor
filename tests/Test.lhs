> module Main where

> import Test.HUnit
> import Control.Monad.Error
> import Text.ParserCombinators.Parsec
> import System

> import Ivor.TT
> import Ivor.Shell

> stdlibShell = addModulePath (newShell emptyContext)
>                  (prefix ++ "/lib/ivor")

> natShell = importFile "nat.tt" stdlibShell
> ackShell = importFile "ack.tt" stdlibShell
> partialShell = importFile "partial.tt" stdlibShell
> vectShell = importFile "vect.tt" stdlibShell

> doEval :: ShellState -> String -> String
> doEval st tm = case (parse (shellParseTerm st) "(test)" tm) of
>                   Left err -> "Parse error: " ++ show err
>                   Right vtm -> case check (getContext st) vtm of
>                       Left str -> "Type error: " ++ str
>                       Right v -> show $ view $ eval (getContext st) v

> nat1 st = doEval st "plus (S (S O)) (S (S O))"
> ack1 st = doEval st "runack 3 4"
> partial1 st = doEval st "fact (S (S (S O)))"
> vect1 st = doEval st "lookup _ _ (fz (S (S O))) (vcons _ _ O (vcons _ _ (S O) (vcons _ _ (S (S O)) (vnil Nat))))"
> vect2 st = doEval st "lookup _ _ (fs _ (fz (S O))) (vcons _ _ O (vcons _ _ (S O) (vcons _ _ (S (S O)) (vnil Nat))))"
> vect3 st = doEval st "lookup _ _ (fs _ (fs _ (fz O))) (vcons _ _ O (vcons _ _ (S O) (vcons _ _ (S (S O)) (vnil Nat))))"

> tests :: IO Test
> tests = do
>    nat <- natShell
>    ack <- ackShell
>    partial <- partialShell
>    vect <- vectShell
>    return $ test ["nat1" ~: "2+2" ~: "S (S (S (S O)))" ~=? nat1 nat,
>                   "ack1" ~: "ack 3 4" ~: "125" ~=? ack1 ack,
>                   "partial1" ~: "partialfact" ~: "Later Nat (Later Nat (Later Nat (Now Nat (S (S (S (S (S (S O)))))))))" ~=? partial1 partial,
>                   "vect1" ~: "lookup 0 [0,1,2]" ~: "O" ~=? vect1 vect,
>                   "vect2" ~: "lookup 1 [0,1,2]" ~: "S O" ~=? vect2 vect,
>                   "vect3" ~: "lookup 2 [0,1,2]" ~: "S (S O)" ~=? vect3 vect]

> main = do 
>    t <- tests
>    counts <- runTestTT t
>    if errors counts + failures counts == 0
>       then exitWith ExitSuccess
>       else exitWith (ExitFailure 1)
