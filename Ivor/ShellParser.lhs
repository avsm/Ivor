> module Ivor.ShellParser(Command(..),
>                           RunTactic(..),
>                           Input(..),
>                           parseInput) where

> import Ivor.TT hiding (try,check,eval)
> import Ivor.TermParser

> import Text.ParserCombinators.Parsec
> import Text.ParserCombinators.Parsec.Language
> import qualified Text.ParserCombinators.Parsec.Token as PTok
> import Control.Monad

> import Debug.Trace

> type TokenParser a = PTok.TokenParser a

> lexer :: TokenParser ()
> lexer = PTok.makeTokenParser haskellDef

> whiteSpace= PTok.whiteSpace lexer
> lexeme    = PTok.lexeme lexer
> symbol    = PTok.symbol lexer
> natural   = PTok.natural lexer
> parens    = PTok.parens lexer
> semi      = PTok.semi lexer
> identifier= PTok.identifier lexer
> reserved  = PTok.reserved lexer
> operator  = PTok.operator lexer
> reservedOp= PTok.reservedOp lexer
> lchar = lexeme.char

> readToEnd :: Parser String
> readToEnd = do term <- many1 $ noneOf ";"
>                return term
>

> data Command = Def String ViewTerm
>              | TypedDef String ViewTerm ViewTerm
>              | PatternDef String ViewTerm Patterns [PattOpt]
>              | Data Inductive
>              | Axiom String ViewTerm
>              | Declare String ViewTerm
>              | DeclareData String ViewTerm
>              | Theorem String ViewTerm
>              | Interactive String ViewTerm
>              | Forget String
>              | EvalTerm ViewTerm
>              | WHNF ViewTerm
>              | Print String
>              | Check ViewTerm
>              | ReplData String String String
>              | Freeze String
>              | Thaw String
>              | Suspend
>              | Resume String
>              | Load FilePath
>              | Plugin FilePath
>              | Compile String
>              | Focus String
>              | Dump String
>              | Undo
>              | Prf
>              | PrfState
>              | Qed
>              | GenRec String
>              | JMEq String String
>              | Primitives
>              | Drop
>              | UserCommand String String

> data RunTactic = Attack
>                | AttackWith String
>                | Claim String ViewTerm
>                | Local String ViewTerm
>                | Refine ViewTerm [ViewTerm]
>                | Solve
>                | Fill ViewTerm
>                | ReturnTac
>                | QuoteTac
>                | CallTac ViewTerm
>                | Abandon
>                | Rename String
>                | Intro
>                | IntroName String
>                | Intros
>                | IntrosNames [String]
>                | AddArg String ViewTerm
>                | Equiv ViewTerm
>                | Generalise Bool ViewTerm
>                | Replace ViewTerm Bool
>                | Axiomatise String [String]
>                | Normalise
>                | Unfold String
>                | Trivial
>                | Split | LeftCon | RightCon | AutoSolve
>                | Exists ViewTerm
>                | By ViewTerm
>                | Induction ViewTerm
>                | Cases ViewTerm
>                | Decide ViewTerm
>                | UserTactic String String

A user defined tactic is a pair of the tactic name, and the function
which runs it.

> data Input = Command Command
>            | Tactic Goal RunTactic

> def :: Maybe (Parser ViewTerm) -> Parser Command
> def ext
>     = do name <- identifier
>          lchar '='
>          term <- pTerm ext ; semi
>          return $ Def name term

> typeddef :: Maybe (Parser ViewTerm) -> Parser Command
> typeddef ext
>     = do reserved "Let"
>          name <- identifier ; lchar ':'; ty <- pTerm ext
>          lchar '=' ; term <- pTerm ext ; semi
>          return $ TypedDef name term ty

> pclause :: String -> Maybe (Parser ViewTerm) -> Parser PClause
> pclause nm ext
>     = do name <- identifier;
>          when (name /= nm) $ fail $ show nm ++ " & " ++ show name ++ " do not match"
>          args <- many (pNoApp ext)
>          try (pclauseret args ext) <|> pclausewith nm args ext

> pclauseret :: [ViewTerm] -> Maybe (Parser ViewTerm) -> Parser PClause
> pclauseret args ext = do lchar '='
>                          ret <- pTerm ext
>                          return $ PClause args [] ret

> pclausewith :: String -> [ViewTerm] -> Maybe (Parser ViewTerm) -> Parser PClause
> pclausewith nm args ext = do lchar '|'
>                              scr <- pTerm ext
>                              lchar '{'
>                              pats <- ppatterns nm ext
>                              lchar '}'
>                              return $ PWithClause False args scr pats

> ppatterns :: String -> Maybe (Parser ViewTerm) -> Parser Patterns
> ppatterns name ext
>     = do clauses <- sepBy (pclause name ext) (lchar '|' )
>          return $ Patterns clauses

> pPattOpt :: Parser PattOpt
> pPattOpt = do reserved "Partial"
>               return Partial
>            <|> do reserved "Rec"
>                   return Ivor.TT.GenRec

> ppatternDef :: Maybe (Parser ViewTerm) -> Parser Command
> ppatternDef ext
>     = do reserved "Match"
>          opts <- many pPattOpt
>          name <- identifier ; lchar ':' ; ty <- pTerm ext
>          lchar '='
>          patts <- ppatterns name ext
>          semi
>          return $ PatternDef name ty patts opts

> pdata :: Maybe (Parser ViewTerm) -> Parser Command
> pdata ext = do reserved "Data"
>                datadef <- pInductive ext ; semi
>                return $ Data datadef

> plata :: Maybe (Parser ViewTerm) -> Parser Command
> plata ext = do reserved "Data"
>                name <- identifier
>                lchar ':'
>                term <- pTerm ext ; semi
>                return $ DeclareData name term

> axiom :: Maybe (Parser ViewTerm) -> Parser Command
> axiom ext
>       = do reserved "Axiom"
>            name <- identifier
>            lchar ':'
>            term <- pTerm ext ; semi
>            return $ Axiom name term

> pdeclare :: Maybe (Parser ViewTerm) -> Parser Command
> pdeclare ext
>       = do reserved "Declare"
>            name <- identifier
>            lchar ':'
>            term <- pTerm ext ; semi
>            return $ Declare name term

> ptheorem :: Maybe (Parser ViewTerm) -> Parser Command
> ptheorem ext
>          = do name <- identifier
>               lchar ':'
>               term <- pTerm ext ; semi
>               return $ Theorem name term

> pinter :: Maybe (Parser ViewTerm) -> Parser Command
> pinter ext
>          = do reserved "Rec"
>               name <- identifier
>               lchar ':'
>               term <- pTerm ext ; semi
>               return $ Interactive name term

> pforget :: Parser Command
> pforget = do reserved "Forget"
>              name <- identifier ; semi
>              return $ Forget name

> eval :: Maybe (Parser ViewTerm) -> Parser Command
> eval ext
>      = do reserved "Eval"
>           term <- pTerm ext ; semi
>           return $ EvalTerm term

> pwhnf :: Maybe (Parser ViewTerm) -> Parser Command
> pwhnf ext
>      = do reserved "Whnf"
>           term <- pTerm ext ; semi
>           return $ WHNF term

> pprint :: Parser Command
> pprint = do reserved "Print"
>             term <- identifier ; semi
>             return $ Print term

> check :: Maybe (Parser ViewTerm) -> Parser Command
> check ext
>       = do reserved "Check"
>            term <- pTerm ext ; semi
>            return $ Check term

> pdrop :: Parser Command
> pdrop = do reserved "Drop" ; semi
>            return Drop

> pprims :: Parser Command
> pprims = do reserved "Primitives" ; semi
>             return Primitives

> pqed :: Parser Command
> pqed = do reserved "Qed" ; semi
>           return Qed

> pgenrec :: Parser Command
> pgenrec = do reserved "General" ;
>              nm <- identifier ; semi
>              return $ Ivor.ShellParser.GenRec nm

> pjme :: Parser Command
> pjme = do reserved "Equality" ;
>           nm <- identifier
>           con <- identifier
>           semi
>           return $ JMEq nm con

> pprf :: Parser Command
> pprf = do reserved "ProofTerm" ; semi
>           return Prf

> pprfstate :: Parser Command
> pprfstate = do reserved "State" ; semi
>                return PrfState

> pundo :: Parser Command
> pundo = do reserved "Undo" ; semi
>            return Undo

> repldata :: Parser Command
> repldata = do reserved "Repl"
>               eq <- identifier
>               repl <- identifier
>               sym <- identifier
>               return $ ReplData eq repl sym

> pfreeze :: Parser Command
> pfreeze = do reserved "Freeze"
>              term <- identifier ; semi
>              return $ Freeze term

> pthaw :: Parser Command
> pthaw = do reserved "Thaw"
>            term <- identifier ; semi
>            return $ Thaw term

> pfocus :: Parser Command
> pfocus = do reserved "Focus"
>             name <- identifier ; semi
>             return $ Focus name

> pdump :: Parser Command
> pdump = do reserved "Dump"
>            name <- option "" identifier ; semi
>            return $ Dump name

> psuspend :: Parser Command
> psuspend = do reserved "Suspend" ; semi
>               return Suspend

> presume :: Parser Command
> presume = do reserved "Resume"
>              nm <- identifier ; semi
>              return $ Resume nm

> pload :: Parser Command
> pload = do reserved "Load"
>            lchar '"' ; rest <- many $ noneOf ['"'] ; lchar '"' ;
>            whiteSpace ; semi
>            return $ Load rest

> pplugin :: Parser Command
> pplugin = do reserved "Plugin"
>              lchar '"' ; rest <- many $ noneOf ['"'] ; lchar '"' ;
>              whiteSpace ; semi
>              return $ Plugin rest

> pcompile :: Parser Command
> pcompile = do reserved "Compile"
>               lchar '"' ; rest <- many $ noneOf ['"'] ; lchar '"' ;
>               whiteSpace ; semi
>               return $ Compile rest

> puser :: [String] -> Parser Command
> puser coms = do com <- identifier ;
>                 if (com `elem` coms)
>                    then do tm <- readToEnd ; semi
>                            return $ UserCommand com tm
>                    else fail "No such command"

> tryall :: [Parser a] -> Parser a
> tryall [x] = x
> tryall (x:xs) = try x <|> tryall xs

> command :: Maybe (Parser ViewTerm) -> [String] -> Parser Command
> command ext user
>             = tryall [def ext, typeddef ext, pdata ext, plata ext,
>                       axiom ext,
>                       ptheorem ext, pdeclare ext, pinter ext, pforget,
>                       eval ext, pwhnf ext, check ext, ppatternDef ext,
>                       pdrop, repldata, pqed, pprint, pfreeze, pthaw, pprf,
>                       pundo, psuspend, presume, pgenrec, pjme,
>                       pload, pcompile, pfocus, pdump, pprfstate, pprims,
>                       pplugin, puser user]

> tactic :: Maybe (Parser ViewTerm) -> [String] -> Parser RunTactic
> tactic ext usertacs
>        = do reserved "attack" ; semi ; return Attack
>      <|> do reserved "attack" ; nm <- identifier ; semi ;
>             return $ AttackWith nm
>      <|> do reserved "claim" ; name <- identifier ; lchar ':' ;
>             tm <- pTerm ext ; semi ; return $ Claim name tm
>      <|> do reserved "local" ; name <- identifier ; lchar ':' ;
>             tm <- pTerm ext ; semi ; return $ Local name tm
>      <|> do reserved "refine" ; nm <- pNoApp ext ;
>             args <- many (pNoApp ext) ;
>             return $ Refine nm args
>      <|> do reserved "solve" ; semi ; return Solve
>      <|> do reserved "fill" ; tm <- pTerm ext ; semi ;
>             return $ Fill tm
>      <|> do reserved "return" ; semi ; return ReturnTac
>      <|> do reserved "quote" ; semi ; return QuoteTac
>      <|> do reserved "call" ; tm <- pTerm ext ; semi ;
>             return $ CallTac tm
>      <|> do reserved "abandon" ; semi ; return Abandon
>      <|> do reserved "rename" ; nm <- identifier ; semi ;
>             return $ Rename nm
>      <|> try (do reserved "intro" ; nms <- many1 identifier; semi
>                  return $ IntrosNames nms)
>      <|> do reserved "intro" ; semi ; return Intro
>      <|> do reserved "intros" ; semi ; return Intros
>      <|> do reserved "arg"; nm <- identifier ; lchar ':';
>             tm <- pTerm ext ; semi ;
>             return $ AddArg nm tm
>      <|> do reserved "equiv" ; tm <- pTerm ext ; semi ;
>             return $ Equiv tm
>      <|> do reserved "generalise" ; dep <- possible "dependent";
>             tm <- pTerm ext ; semi ;
>             return $ Generalise dep tm
>      <|> do reserved "replace" ; sym <- possible "sym";
>             tm <- pTerm ext ; semi ;
>             return $ Replace tm (not sym)
>      <|> do reserved "axiomatise" ; nm <- identifier ;
>             nms <- many identifier; semi ;
>             return $ Axiomatise nm nms
>      <|> do reserved "compute" ; semi ; return Normalise
>      <|> do reserved "unfold" ; nm <- identifier ;
>             semi ; return $ Unfold nm
>      <|> do reserved "trivial" ; semi ; return Trivial
>      <|> do reserved "split" ; semi ; return Split
>      <|> do reserved "left" ; semi ; return LeftCon
>      <|> do reserved "right" ; semi ; return RightCon
>      <|> do reserved "exists" ; tm <- pTerm ext ; semi ;
>             return $ Exists tm
>      <|> do reserved "auto" ; semi ; return AutoSolve
>      <|> do reserved "by" ; tm <- pTerm ext ; semi ;
>             return $ By tm
>      <|> do reserved "induction" ; tm <- pTerm ext ; semi ;
>             return $ Induction tm
>      <|> do reserved "case" ; tm <- pTerm ext ; semi ;
>             return $ Cases tm
>      <|> do reserved "decide" ; tm <- pTerm ext ; semi ;
>             return $ Decide tm
>      <|> do tac <- identifier ;
>             if (tac `elem` usertacs)
>                then do tm <- readToEnd ; semi
>                        return $ UserTactic tac tm
>                else fail "No such tactic"

> possible :: String -> Parser Bool
> possible word = option False (do reserved word ; return True)

> input :: Maybe (Parser ViewTerm) -> [String] -> [String] -> Parser Input
> input ext usertacs usercoms
>           = try (do whiteSpace
>                     cmd <- command ext usercoms
>                     return $ Command cmd)
>             <|> (do whiteSpace
>                     tac <- tactic ext usertacs
>                     return $ Tactic defaultGoal tac)

> parseInput :: Monad m => Maybe (Parser ViewTerm) ->
>                          [String] -> [String] -> String -> m Input
> parseInput ext usertacs usercoms str
>     = case parse (input ext usertacs usercoms) "(input)" str of
>                 Left err -> fail (show err)
>                 Right inp -> return inp
