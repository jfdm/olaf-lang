module Olaf.Syntax.Lispy

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

  typeList : Rule Ty
  typeList =
    do symbol "("
       keyword "List"
       ty <- type
       symbol ")"
       pure (TyList ty)

  typeSum : Rule Ty
  typeSum =
    do symbol "("
       keyword "Sum"
       a <- type
       b <- type
       symbol ")"
       pure (TySum a b)

  typeProduct : Rule Ty
  typeProduct =
    do symbol "("
       keyword "Pair"
       a <- type
       b <- type
       symbol ")"
       pure (TyProduct a b)

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
      <|> gives "String" (const TyString)
      <|> gives "Char"   (const TyChar)
      <|> gives "Unit"   (const TyUnit)
      <|> typeList
      <|> typeSum
      <|> typeProduct
      <|> typeFunc

bool : Rule Expr
bool =  gives "true"  (\x => B x True)
    <|> gives "false" (\x => B x False)

prim : Rule Expr
prim =  ref
    <|> inserts natLit  N
    <|> inserts charLit C
    <|> inserts strLit  S
    <|> bool

mutual
  tuple : Rule Expr
  tuple =
    do s <- Toolkit.location
       symbol "("
       a <- expr
       symbol ","
       b <- expr
       symbol ")"
       e <- Toolkit.location
       pure (Pair (newFC s e) a b)

  listExt : Rule Expr
  listExt =
     do s <- Toolkit.location
        symbol "("
        keyword "extend"
        h <- expr
        t <- expr
        symbol ")"
        e <- Toolkit.location
        pure (Extend (newFC s e) h t)

  empty : Rule Expr
  empty =
    do s <- Toolkit.location
       keyword "empty"
       symbol "["
       ty <- type
       symbol "]"
       e <- Toolkit.location
       pure (Empty (newFC s e) ty)

  primOp : Rule Expr
  primOp = uOp <|> bOp
    where
      uOpKind : Rule (tyA ** tyB ** UnOp tyA tyB)
      uOpKind =  gives "not" (const (_ ** _ ** BNot))
             <|> gives "size" (const (_ ** _ ** SOp SIZE))
             <|> gives "pack" (const (_ ** _ ** SOp PACK))
             <|> gives "unpack" (const (_ ** _ ** SOp UNPACK))
             <|> gives "toString" (const (_ ** _ ** COp TOSTR))
             <|> gives "toNat" (const (_ ** _ ** COp ORD))
             <|> gives "toChar" (const (_ ** _ ** COp CHAR))

      uOp : Rule Expr
      uOp =
        do s <- Toolkit.location
           symbol "("
           k <- uOpKind
           o <- (ref <|> expr)
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
           a <- (ref <|> expr)
           b <- (ref <|> expr)
           symbol ")"
           e <- Toolkit.location
           pure (BOp (newFC s e) (snd (snd k)) a b)


  this, that : Rule Expr
  this =
    do s <- Toolkit.location
       symbol "("
       keyword "this"
       t <- (ref <|> expr)
       keyword "as"
       ty <- type
       symbol ")"
       e <- Toolkit.location
       pure (This (newFC s e) t ty)

  that =
    do s <- Toolkit.location
       symbol "("
       keyword "that"
       t <- (ref <|> expr)
       keyword "as"
       ty <- type
       symbol ")"
       e <- Toolkit.location
       pure (That (newFC s e) t ty)

  funAnon : Rule Expr
  funAnon =
    do s <- Toolkit.location
       symbol "("
       keyword "fun"
       symbol "("
       args <- some (do a <- Toolkit.location
                        symbol "["
                        n <- name
                        symbol ":"
                        ty <- type
                        symbol "]"
                        b <- Toolkit.location
                        pure (newFC a b, n, ty))
       symbol ")"
       body <- expr
       symbol ")"
       e <- Toolkit.location
       pure (foldr (\(fc,n,ty),acc => Fun fc n ty acc) body (forget args))


  cond : Rule Expr
  cond =
    do s <- Toolkit.location
       symbol "("
       keyword "if"
       c <- (ref <|> expr)
       t <- expr
       f <- expr
       symbol ")"
       e <- Toolkit.location
       pure (Cond (newFC s e) c t f)

  let_ : Rule Expr
  let_ = letRec <|> letNonRec
    where
      body : Location -> Bool -> Rule Expr
      body s isRec
        = do symbol "["
             n <- name
             symbol ":"
             ty <- type
             v <- expr
             symbol "]"
             b <- expr
             symbol ")"
             e <- Toolkit.location
             pure (Let (newFC s e) n ty isRec v b)


      letNonRec : Rule Expr
      letNonRec
        = do s <- Toolkit.location
             symbol "("
             keyword "let"
             body s False

      letRec : Rule Expr
      letRec
        = do s <- Toolkit.location
             symbol "("
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

  unit : Rule Expr
  unit = gives "unit" TheUnit

  ascription : Rule Expr
  ascription =
    do s <- Toolkit.location
       symbol "("
       keyword "the"
       ty <- type
       v  <- expr
       symbol ")"
       e <- Toolkit.location
       pure (The (newFC s e) ty v)

  match_pair : Rule Expr
  match_pair
    = do s <- Toolkit.location
         symbol "("
         keyword "match"
         c <- expr
         symbol "["
         symbol "("
         a <- name
         symbol ","
         b <- name
         symbol ")"
         r <- expr
         symbol "]"
         symbol ")"
         e <- Toolkit.location
         pure (MatchPair (newFC s e) c a b r)

  match_list : Rule Expr
  match_list
    = do s <- Toolkit.location
         symbol "("
         keyword "match"
         c <- expr
         symbol "["
         keyword "empty"
         emp <- expr
         symbol "]"
         symbol "["
         symbol "("
         keyword "extend"
         h <- name
         t <- name
         symbol ")"
         rest <- expr
         symbol "]"
         symbol ")"
         e <- Toolkit.location
         pure (MatchList (newFC s e) c emp h t rest)

  match_sum : Rule Expr
  match_sum
    = do s <- Toolkit.location
         symbol "("
         keyword "match"
         c <- expr
         symbol "["
         symbol "("
         keyword "this"
         l <- name
         symbol ")"
         bl <- expr
         symbol "]"
         symbol "["
         symbol "("
         keyword "that"
         r <- name
         symbol ")"
         br <- expr
         symbol "]"
         symbol ")"
         e <- Toolkit.location
         pure (MatchSum (newFC s e) c l bl r br)

  expr : Rule Expr
  expr =   ref
       <|> let_
       <|> app
       <|> cond
       <|> match_sum
       <|> match_list
       <|> match_pair
       <|> prim
       <|> primOp
       <|> unit
       <|> this
       <|> that
       <|> listExt
       <|> empty
       <|> tuple
       <|> funAnon
       <|> ascription

main_ : Rule Expr
main_ =
  do s <- Toolkit.location
     symbol "("
     keyword "main"
     v <- expr
     symbol ")"
     e <- Toolkit.location
     pure v


decl : Rule (FileContext, String, Ty, Bool, Expr)
decl = declRec <|> declNonRec
  where
    body : Location -> Bool -> Rule (FileContext, String, Ty, Bool, Expr)
    body s b
      = do symbol "["
           n <- name
           symbol ":"
           t <- type
           symbol "]"
           v <- expr
           symbol ")"
           e <- Toolkit.location
           pure (newFC s e, n, t, b, v)

    declNonRec : Rule (FileContext, String, Ty, Bool, Expr)
    declNonRec
      = do s <- Toolkit.location
           symbol "("
           keyword "def"
           body s False

    declRec : Rule (FileContext, String, Ty, Bool, Expr)
    declRec
      = do s <- Toolkit.location
           symbol "("
           keyword "def"
           keyword "rec"
           body s True

olaf : Rule Expr
olaf =
  do ds <- many decl
     m <- main_
     eoi
     pure (foldr (\(fc, n, ty, rec, v),acc =>
                      Let fc n ty rec v acc)
                 m ds)

namespace Olaf
  namespace Lispy

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
