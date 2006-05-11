> module Main where

> import Test.HUnit
> import Control.Monad.Error
> import Text.ParserCombinators.Parsec
> import System

> import Ivor.TT
> import Ivor.Shell

> natShell = importFile "nat.tt" (newShell initState)
> ackShell = importFile "ack.tt" (newShell initState)
> partialShell = importFile "partial.tt" (newShell initState)

> doEval :: ShellState -> String -> String
> doEval st tm = case (parse (shellParseTerm st) "(test)" tm) of
>                   Left err -> "Parse error: " ++ show err
>                   Right vtm -> case check (getContext st) vtm of
>                       Left str -> "Type error: " ++ str
>                       Right v -> show $ view $ eval (getContext st) v

> nat1 st = doEval st "plus (S (S O)) (S (S O))"
> ack1 st = doEval st "runack 3 4"
> partial1 st = doEval st "fact (S (S (S O)))"

> tests :: IO Test
> tests = do
>    nat <- natShell
>    ack <- ackShell
>    partial <- partialShell
>    return $ test ["nat1" ~: "2+2" ~: "S (S (S (S O)))" ~=? nat1 nat,
>                   "ack1" ~: "ack 3 4" ~: "125" ~=? ack1 ack,
>                   "partial1" ~: "partialfact" ~: "Later Nat (Later Nat (Later Nat (Now Nat (S (S (S (S (S (S O)))))))))" ~=? partial1 partial]

> main = do 
>    t <- tests
>    counts <- runTestTT t
>    if errors counts + failures counts == 0
>       then exitWith ExitSuccess
>       else exitWith (ExitFailure 1)
