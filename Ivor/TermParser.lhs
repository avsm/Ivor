> -- | 
> -- Module      : Ivor.TermParser
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : non-portable
> -- 
> -- Extensible Parsec based parsing library for 'ViewTerm's.
> --
> -- Briefly, the syntax is as follows:
> --
> --  * @[x:A]y@ -- Lambda binding with scope @y@.
> --
> --  * @(x:A) -> B@ -- Forall binding with scope @B@ (@->@ optional).
> --
> --  * @A -> B@ -- Forall binding where name bound is not used in @B@..
> --
> --  * @let x:A=v in y@ -- Let binding, @x=v@ in scope @y@.
> -- 
> --  * @f a@ -- Function application (left associative, by juxtaposition).
> --   
> --  * @[identifier]@ -- names are legal Haskell identifiers.
> --  
> --  * @\*@ -- Asterisk is type of types.
> --
> --  * @_@ -- Underscore is a placeholder.
> --
> -- Lambda\/forall bindings of multiple variables are also accepted,
> -- in the form @[x,y:A;z:B]@
> --
> -- Staging annotations have the following syntax:
> --
> --  * @{'x}@ -- quoted term @x@
> --
> --  * @{{A}}@ -- code type @A@ (if @x:A@, @{'x}:{{A}}@
> --
> --  * @!x@ -- evaluate a quoted term
> --
> --  * @~x@ -- escape a quoted term (i.e. splice into a quoted term)
> -- 
> -- Extensions for labelled types (see McBride\/McKinna \"The View
> -- From The Left\" for details):
> --
> --  * @\<[identifier] args : t\>@ -- Labelled type.
> --
> --  * @call \<label\> term@ -- Call a computation.
> --   
> --  * @return t@ -- Return a value from a computation.
> --

> module Ivor.TermParser(pTerm, pNoApp, pInductive,
>                          parseTermString, parseDataString) where

> import Ivor.ViewTerm
> import Ivor.TTCore(Name(..))

> import Text.ParserCombinators.Parsec
> import Text.ParserCombinators.Parsec.Language
> import qualified Text.ParserCombinators.Parsec.Token as PTok

> import Debug.Trace

> type TokenParser a = PTok.TokenParser a

> lexer :: TokenParser ()
> lexer  = PTok.makeTokenParser haskellDef

> whiteSpace= PTok.whiteSpace lexer
> lexeme    = PTok.lexeme lexer
> symbol    = PTok.symbol lexer
> natural   = PTok.natural lexer
> parens    = PTok.parens lexer
> semi      = PTok.semi lexer
> comma     = PTok.comma lexer
> identifier= PTok.identifier lexer
> reserved  = PTok.reserved lexer
> operator  = PTok.operator lexer
> reservedOp= PTok.reservedOp lexer
> lchar = lexeme.char

> app :: Parser (ViewTerm -> ViewTerm -> ViewTerm)
> app = do whiteSpace ; return App

> arrow :: Parser (ViewTerm -> ViewTerm -> ViewTerm)
> arrow = do symbol "->" ; return $ Forall (name "X")

> -- | Basic parsec combinator for parsing terms.
> pTerm :: Maybe (Parser ViewTerm) -- ^ Extra parse rules (for example 
>          -- for any primitive types or operators you might have added).
>          -> Parser ViewTerm
> pTerm Nothing = try (do chainl1 (pNoApp Nothing) app)
>             <|> (pNoApp Nothing)
>             -- <|> pInfix Nothing
> pTerm (Just ext) = try (do chainl1 (pNoApp (Just ext)) app)
>                    -- <|> try (pInfix (Just ext))
>                    <|> try (pNoApp (Just ext))
>                    <|> ext

> -- | Parse a term which is not an application; 
> -- use for parsing lists of terms.
> pNoApp :: Maybe (Parser ViewTerm) -> Parser ViewTerm
> pNoApp ext = try (do chainr1 (pExp ext) arrow)
>              <|> pExp ext

> pExp :: Maybe (Parser ViewTerm) -> Parser ViewTerm
> pExp ext = 
>        do lchar '[' ; bs <- bindList ext ; lchar ']'
>           sc <- pTerm ext ;
>           return $ bindAll Lambda bs sc
>        <|> try (do lchar '(' ; bs <- bindList ext ; lchar ')'
>                    option "" (symbol "->")
>                    sc <- pTerm ext ;
>                    return $ bindAll Forall bs sc)
>        <|> do reserved "let" ; var <- identifier;
>               lchar ':' ; ty <- pTerm ext ; lchar '=' ; val <- pTerm ext ;
>               reserved "in" ; sc <- pTerm ext ;
>               return $ Let (UN var) ty val sc
>        <|> do lchar '(' ; t <- pTerm ext ; lchar ')' ; return t
>        <|> do lchar '<'
>               (nm,args) <- computation ext ; lchar ':' ; lty <- pTerm ext
>               lchar '>';
>               return $ Label nm args lty
>        <|> do reserved "call" ; lchar '<' 
>               (nm,args) <- computation ext ;
>               lchar '>' ; tm <- pNoApp ext;
>               return $ Call nm args tm
>        <|> do reserved "return"; tm <- pTerm ext;
>               return $ Return tm
>        <|> do nm <- identifier ; return (Name Unknown (UN nm))
>        <|> do lchar '*' ; return Star
>        <|> do lchar '_' ; return Placeholder
>        <|> try (do symbol "{'" ; tm <- pTerm ext; lchar '}'
>                    return $ Quote tm)
>        <|> try (do symbol "{{" ; tm <- pTerm ext; symbol "}}"
>                    return $ Code tm)
>        <|> try (do symbol "!" ; tm <- pNoApp ext;
>                    return $ Eval tm)
>        <|> try (do symbol "~" ; tm <- pNoApp ext;
>                    return $ Escape tm)
>        <|> do case ext of
>                  Nothing -> fail "Parse error"
>                  Just ext -> ext

> -- | Parse an infix expression
> pInfix :: Maybe (Parser ViewTerm) -> Parser ViewTerm
> pInfix ext = do 
>                 lexp <- trace ("Trying = ") $ pNoApp ext
>                 lchar '='
>                 rexp <- trace (show lexp) $ pTerm ext
>                 return $ apply (Name Unknown (name "Eq"))
>                            [Placeholder,Placeholder,lexp,rexp]

> pNoInfix ext = try (do chainl1 (pNoApp ext) app)
>                <|> pNoApp ext

> -- | Basic parsec combinator for parsing inductive data types
> pInductive :: Maybe (Parser ViewTerm) -- ^ Extra parse rules (for example 
>          -- for any primitive types or operators you might have added).
>          -> Parser Inductive
> pInductive ext = do nm <- identifier
>                     parmsM <- many (do lchar '('
>                                        xs <- bindList ext
>                                        lchar ')' ; return xs)
>                     lchar ':'
>                     indicesM <- many (do lchar '('
>                                          xs <- bindList ext
>                                          lchar ')' ; return xs)
>                     ty <- pTerm ext ; lchar '='
>                     cons <- sepBy (constructor ext) (lchar '|')
>                     return $ Inductive (UN nm) 
>                                        (concat parmsM) 
>                                        (concat indicesM)
>                                        ty cons

> constructor ext = do nm <- identifier ; lchar ':'
>                      ty <- pTerm ext
>                      return $ (UN nm,ty)

> bindList :: Maybe (Parser ViewTerm) -> Parser [(Name, ViewTerm)]
> bindList ext 
>     = do namelist <- sepBy1 identifier comma
>          lchar ':'
>          ty <- pTerm ext
>          rest <- option [] (do semi ; bindList ext)
>          return $ (map (\x -> (UN x,ty)) namelist) ++ rest

> bindAll binder [] sc = sc
> bindAll binder ((n,ty):xs) sc = binder n ty (bindAll binder xs sc)

> computation :: Maybe (Parser ViewTerm) -> Parser (Name, [ViewTerm])
> computation ext = do nm <- identifier ; args <- many (pNoApp ext)
>                      return (UN nm, args)

> -- | Parse a string into a ViewTerm, without mucking about with parsec
> -- or any extra parse rules.
> parseTermString :: Monad m => String -> m ViewTerm
> parseTermString str 
>     = case parse (do t <- pTerm Nothing ; eof ; return t) "(input)" str of
>           Left err -> fail (show err)
>           Right tm -> return tm

> -- | Parse a string into an Inductive, without mucking about with parsec
> -- or any extra parse rules.
> parseDataString :: Monad m => String -> m Inductive
> parseDataString str 
>     = case parse (do t <- pInductive Nothing ; eof ; return t) 
>                   "(input)" str of
>           Left err -> fail (show err)
>           Right d -> return d
