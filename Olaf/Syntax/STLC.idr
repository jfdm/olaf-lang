module Olaf.Syntax.STLC

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.String
import Data.Maybe

import Text.Lexer
import Text.Parser

import        Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import        Toolkit.Text.Parser.Support
import        Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import Olaf

import Olaf.AST

import public Olaf.Syntax.Common.Lexer
import        Olaf.Syntax.Common.Parser

%default total

ref : Rule Expr
ref = inserts name Ref

mutual

  typeFunc : Rule Ty
  typeFunc
    = do symbol "("
         a <- type
         arrow
         bs <- type
         symbol ")"
         pure $ TyFunc a bs


  type : Rule Ty
  type =  gives "Nat"    (const TyNat)
      <|> gives "Bool"   (const TyBool)
      <|> typeFunc

bool : Rule Expr
bool =  gives "true"  (\x => B x True)
    <|> gives "false" (\x => B x False)

prim : Rule Expr
prim =  inserts natLit  N
    <|> bool

mutual

  primOp : Rule Expr
  primOp = uOp <|> bOp
    where
      uOpKind : Rule (tyA ** tyB ** UnOp tyA tyB)
      uOpKind =  gives "not" (const (_ ** _ ** BNot))

      uOp : Rule Expr
      uOp =
        do s <- Toolkit.location
           symbol "("
           k <- uOpKind
           o <- expr
           symbol ")"
           e <- Toolkit.location
           pure (UOp (newFC s e) (snd (snd k)) o)

      bOpKind : Rule (tyA ** tyB ** BinOp tyA tyB)
      bOpKind =  gives "lessThan" (const (_ ** _ ** NCmp))
             <|> gives "add" (const (_ ** _ ** NOp PLUS))
             <|> gives "sub" (const (_ ** _ ** NOp SUB))
             <|> gives "and" (const (_ ** _ ** BOp AND))
             <|> gives "or" (const (_ ** _ ** BOp OR))
             <|> gives "xor" (const (_ ** _ ** BOp XOR))

      bOp : Rule Expr
      bOp =
        do s <- Toolkit.location
           symbol "("
           k <- bOpKind
           a <- expr
           b <- expr
           symbol ")"
           e <- Toolkit.location
           pure (BOp (newFC s e) (snd (snd k)) a b)

  funAnon : Rule Expr
  funAnon =
    do s <- Toolkit.location
       symbol "("
       keyword "fun"
       n <- name
       symbol ":"
       ty <- type
       suchThat
       body <- expr
       symbol ")"
       e <- Toolkit.location
       pure (Fun (newFC s e) n ty body)


  cond : Rule Expr
  cond =
    do s <- Toolkit.location
       keyword "if"
       c <- (ref <|> expr)
       keyword "then"
       t <- expr
       keyword "else"
       f <- expr
       e <- Toolkit.location
       pure (Cond (newFC s e) c t f)

  let_ : Rule Expr
  let_ = letRec <|> letNonRec
    where
      body : Location -> Bool -> Rule Expr
      body s isRec
        = do n <- name
             symbol ":"
             ty <- type
             assign
             v <- expr
             keyword "in"
             b <- expr
             e <- Toolkit.location
             pure (Let (newFC s e) n ty isRec v b)


      letNonRec : Rule Expr
      letNonRec
        = do s <- Toolkit.location
             keyword "let"
             body s False

      letRec : Rule Expr
      letRec
        = do s <- Toolkit.location
             keyword "let"
             keyword "rec"
             body s True

  app : Rule Expr
  app =
    do s <- Toolkit.location
       symbol "("
       f <- expr
       a <- expr
       symbol ")"
       e <- Toolkit.location
       pure (App (newFC s e) f a)

  expr : Rule Expr
  expr =   ref
       <|> let_
       <|> app
       <|> cond
       <|> prim
       <|> primOp
       <|> funAnon


olaf : Rule Expr
olaf = expr

namespace Olaf
  namespace STLC

    namespace Expression
      export
      fromString : (str : String)
                       -> (Either (ParseError Token) Expr)
      fromString str
        = parseString Olaf.lexer expr str

    namespace Programme
      export
      fromFile : (fname : String)
                       -> IO (Either (ParseError Token) Expr)
      fromFile fname
        = case !(parseFile Olaf.lexer olaf fname) of
            Left err  => pure (Left err)
            Right ast => pure (Right (map (setSource fname) ast))

-- [ EOF ]
