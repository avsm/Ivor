> {-# OPTIONS_GHC -fglasgow-exts #-}

> -- | 
> -- Module      : Ivor.Primitives
> -- Copyright   : Edwin Brady
> -- Licence     : BSD-style (see LICENSE in the distribution)
> --
> -- Maintainer  : eb@dcs.st-and.ac.uk
> -- Stability   : experimental
> -- Portability : portable
> -- 
> -- Some basic primitive types. Importing this module adds instances
> -- of 'ViewConst' for Int, Float and String (Float is represented by
> -- Haskell Double). 'addPrimitives' should be
> -- used to add these type constructors to the context.

> module Ivor.Primitives(addPrimitives, parsePrimitives, 
>                          parsePrimTerm) 
>     where

> import Ivor.TT hiding (try)
> import Ivor.TermParser
> import Ivor.ViewTerm

> import Text.ParserCombinators.Parsec
> import Text.ParserCombinators.Parsec.Language
> import qualified Text.ParserCombinators.Parsec.Token as PTok

> type TokenParser a = PTok.TokenParser a

> lexer :: TokenParser ()
> lexer  = PTok.makeTokenParser haskellDef

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
> stringlit = PTok.stringLiteral lexer
> float     = PTok.float lexer
> lchar = lexeme.char

> instance ViewConst Int where
>     typeof x = (name "Int")

> instance ViewConst Double where
>     typeof x = (name "Float")

> instance ViewConst String where
>     typeof x = (name "String")

> -- | Add primitive types for Int, Float and String, and some
> -- primitive operations [add,sub,mult,div][int,float] and concat.

> addPrimitives :: Monad m => Context -> m Context
> addPrimitives c = do c <- addPrimitive c (name "Int")
>                      c <- addPrimitive c (name "Float")
>                      c <- addPrimitive c (name "String")
>                      c <- addBinOp c (name "addInt") ((+)::Int->Int->Int) 
>                               "(x:Int)(y:Int)Int"
>                      c <- addBinOp c (name "subInt") ((-)::Int->Int->Int) 
>                               "(x:Int)(y:Int)Int"
>                      c <- addBinOp c (name "multInt") ((*)::Int->Int->Int) 
>                               "(x:Int)(y:Int)Int"
>                      c <- addBinOp c (name "divInt") 
>                               ((div)::Int->Int->Int) 
>                               "(x:Int)(y:Int)Int"
>                      c <- addBinOp c (name "addFloat") 
>                               ((+)::Double->Double->Double) 
>                               "(x:Float)(y:Float)Float"
>                      c <- addBinOp c (name "subFloat") 
>                               ((-)::Double->Double->Double) 
>                               "(x:Float)(y:Float)Float"
>                      c <- addBinOp c (name "multFloat") 
>                                ((*)::Double->Double->Double) 
>                               "(x:Float)(y:Float)Float"
>                      c <- addBinOp c (name "divFloat") 
>                                ((/)::Double->Double->Double) 
>                               "(x:Float)(y:Float)Float"
>                      c <- addBinOp c (name "concat") 
>                               ((++)::String->String->String) 
>                               "(x:String)(y:String)String"
>                      c <- addPrimFn c (name "intToNat") intToNat
>                               "(x:Int)Nat"
>                      c <- addPrimFn c (name "intToString") 
>                               intToString
>                               "(x:Int)String"
>                      return c

> intToNat :: Int -> ViewTerm
> intToNat 0 = Name DataCon (name "O")
> intToNat n = App (Name DataCon (name "S")) (intToNat (n-1))

> intToString :: Int -> ViewTerm
> intToString n = Constant (show n)

> -- | Parse a primitive constant

> parsePrimitives :: Parser ViewTerm
> parsePrimitives = try (do x <- float
>                           return $ Constant x)
>               <|> do x <- stringlit
>                      return $ Constant x
>               <|> do x <- parseInt
>                      return $ Constant x

> parseInt :: Parser Int
> parseInt = lexeme $ fmap read (many1 digit)

> -- | Parse a term including primitives
> parsePrimTerm :: Monad m => String -> m ViewTerm
> parsePrimTerm str
>     = case parse (do t <- pTerm (Just parsePrimitives) ; eof ; return t) 
>                  "(input)" str of
>           Left err -> fail (show err)
>           Right tm -> return tm

 
