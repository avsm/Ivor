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
> pattShell = importFile "patt.tt" stdlibShell

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

> patt1 st = doEval st "treeSum _ testTree"
> patt2 st = doEval st "vtail _ _ testvec"
> patt3 st = doEval st "vadd _ (vcons _ _ (S (S (S O))) (vcons _ _ (S (S O)) (vnil Nat))) (vcons _ _ (S (S (S O))) (vcons _ _ (S (S O)) (vnil Nat)))"
> patt4 st = doEval st "vlookup _ _ (fs _ (fz _)) testvec"
> patt5 st = doEval st "minus (S (S (S O))) (S O) (leS _ _ (leO _))"
> patt6 st = doEval st "envlookup _ (fs _ (fz _)) _ testValEnv"


> tests :: IO Test
> tests = do
>    nat <- natShell
>    ack <- ackShell
>    partial <- partialShell
>    vect <- vectShell
>    patt <- pattShell
>    return $ test ["nat1" ~: "2+2" ~: "S (S (S (S O)))" ~=? nat1 nat,
>                   "ack1" ~: "ack 3 4" ~: "125" ~=? ack1 ack,
>                   "partial1" ~: "partialfact" ~: "Later Nat (Later Nat (Later Nat (Now Nat (S (S (S (S (S (S O)))))))))" ~=? partial1 partial,
>                   "vect1" ~: "lookup 0 [0,1,2]" ~: "O" ~=? vect1 vect,
>                   "vect2" ~: "lookup 1 [0,1,2]" ~: "S O" ~=? vect2 vect,
>                   "vect3" ~: "lookup 2 [0,1,2]" ~: "S (S O)" ~=? vect3 vect,
>                   "patt1" ~: "treesum" ~: "S (S (S (S O)))" ~=? patt1 patt,
>                   "patt2" ~: "vtail" ~: "vcons Nat (S O) (S (S (S O))) (vcons Nat O (S (S O)) (vnil Nat))" ~=? patt2 patt,
>                   "patt3" ~: "vadd" ~: "vcons Nat (S O) (S (S (S (S (S (S O)))))) (vcons Nat O (S (S (S (S O)))) (vnil Nat))" ~=? patt3 patt,
>                   "patt4" ~: "vlookup" ~: "S (S (S O))" ~=? patt4 patt,
>                   "patt5" ~: "3-1" ~: "S (S O)" ~=? patt5 patt,
>                   "patt6" ~: "envlookup" ~: "false" ~=? patt6 patt]

> main = do 
>    t <- tests
>    counts <- runTestTT t
>    if errors counts + failures counts == 0
>       then exitWith ExitSuccess
>       else exitWith (ExitFailure 1)
