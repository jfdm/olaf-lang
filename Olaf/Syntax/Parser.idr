module Olaf.Syntax.Parser

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.Strings
import Data.Maybe

import Text.Lexer
import Text.Parser

import Toolkit.Data.Location
import public Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location
import public Toolkit.Text.Parser.Run

import Olaf

import Olaf.Syntax.Lexer
import Olaf.Syntax.AST

%default total

namespace API

  export
  eoi : RuleEmpty Token ()
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False

  export
  symbol : String -> Rule Token ()
  symbol str
    = terminal ("Expected Symbol '" ++ str ++ "'")
               (\x => case tok x of
                             Symbol s => if s == str then Just ()
                                                     else Nothing
                             _ => Nothing)

  export
  arrow : Rule Token ()
  arrow = symbol "->"

  export
  assign : Rule Token ()
  assign = symbol ":="

  export
  suchThat : Rule Token ()
  suchThat = symbol "=>"

  export
  keyword : String -> Rule Token ()
  keyword str
    = terminal ("Expected Keyword '" ++ str ++ "'")
                 (\x => case tok x of
                             Keyword s => if s == str then Just ()
                                                      else Nothing
                             _ => Nothing)

  export
  natLit : Rule Token Nat
  natLit = terminal "Expected nat literal"
               (\x => case tok x of
                           LitNat i => Just i
                           _ => Nothing)

  export
  strLit : Rule Token String
  strLit = terminal "Expected string literal"
               (\x => case tok x of
                           LitStr i => Just i
                           _ => Nothing)

  export
  charLit : Rule Token Char
  charLit = terminal "Expected string literal"
               (\x => case tok x of
                           LitChr i =>
                             case unpack i of
                               Nil => Just '\0000'
                               [x] => Just x
                               _   => Nothing
                           _ => Nothing)


  export
  identifier : Rule Token String
  identifier
    = terminal "Expected Identifier"
               (\x => case tok x of
                                  ID str => Just str
                                  _ => Nothing)

  export
  name : Rule Token String
  name = identifier

  export
  parens : Inf (Rule Token a)
        -> Rule Token a
  parens = between (symbol "(") (symbol ")")

  export
  arrowSepBy1 : Rule Token a -> Rule Token (List1 a)
  arrowSepBy1 = sepBy1 arrow

  export
  commaSepBy1 : Rule Token a -> Rule Token (List1 a)
  commaSepBy1 = sepBy1 (symbol ",")

  export
  gives : String -> (FileContext -> a) -> Rule Token a
  gives s ctor
    = do a <- location
         keyword s
         b <- location
         pure (ctor (newFC a b))


  export
  inserts : Rule Token a -> (FileContext -> a -> b) -> Rule Token b
  inserts value ctor
    = do a <- location
         v <- value
         b <- location
         pure (ctor (newFC a b) v)

ref : Rule Token Expr
ref = inserts name    Ref

mutual

  typeList : Rule Token Ty
  typeList =
    do symbol "("
       keyword "List"
       ty <- type
       symbol ")"
       pure (TyList ty)

  typeSum : Rule Token Ty
  typeSum =
    do symbol "("
       keyword "Sum"
       a <- type
       b <- type
       symbol ")"
       pure (TySum a b)

  typeProduct : Rule Token Ty
  typeProduct =
    do symbol "("
       keyword "Pair"
       a <- type
       b <- type
       symbol ")"
       pure (TyProduct a b)

  typeFunc : Rule Token Ty
  typeFunc
    = do symbol "("
         a <- type
         arrow
         bs <- type
         symbol ")"
         pure $ TyFunc a bs


  type : Rule Token Ty
  type =  typeFunc
      <|> typeList
      <|> typeSum
      <|> typeProduct
      <|> gives "Nat"    (const TyNat)
      <|> gives "Bool"   (const TyBool)
      <|> gives "String" (const TyString)
      <|> gives "Char"   (const TyChar)
      <|> gives "Unit"   (const TyUnit)

bool : Rule Token Expr
bool =  gives "true"  (\x => B x True)
    <|> gives "false" (\x => B x False)

prim : Rule Token Expr
prim =  ref
    <|> inserts natLit  N
    <|> inserts charLit C
    <|> inserts strLit  S
    <|> bool

mutual
  tuple : Rule Token Expr
  tuple =
    do s <- location
       symbol "("
       a <- expr
       symbol ","
       b <- expr
       symbol ")"
       e <- location
       pure (Pair (newFC s e) a b)

  listExt : Rule Token Expr
  listExt =
     do s <- location
        symbol "("
        keyword "extend"
        h <- expr
        t <- expr
        symbol ")"
        e <- location
        pure (Extend (newFC s e) h t)

  empty : Rule Token Expr
  empty =
    do s <- location
       keyword "empty"
       symbol "["
       ty <- type
       symbol "]"
       e <- location
       pure (Empty (newFC s e) ty)

  primOp : Rule Token Expr
  primOp = uOp <|> bOp
    where
      uOpKind : Rule Token UnOp
      uOpKind =  gives "not" (const BNot)
             <|> gives "size" (const (SOp SIZE))
             <|> gives "pack" (const (SOp PACK))
             <|> gives "unpack" (const (SOp UNPACK))
             <|> gives "toString" (const (COp TOSTR))
             <|> gives "toNat" (const (COp ORD))
             <|> gives "toChar" (const (COp CHAR))

      uOp : Rule Token Expr
      uOp =
        do s <- location
           symbol "("
           k <- uOpKind
           o <- (ref <|> expr)
           symbol ")"
           e <- location
           pure (UOp (newFC s e) k o)

      bOpKind : Rule Token BinOp
      bOpKind =  gives "lessThan" (const NCmp)
             <|> gives "add" (const (NOp PLUS))
             <|> gives "sub" (const (NOp SUB))
             <|> gives "and" (const (BOp AND))
             <|> gives "or" (const (BOp OR))
             <|> gives "xor" (const (BOp XOR))

      bOp : Rule Token Expr
      bOp =
        do s <- location
           symbol "("
           k <- bOpKind
           a <- (ref <|> expr)
           b <- (ref <|> expr)
           symbol ")"
           e <- location
           pure (BOp (newFC s e) k a b)


  this, that : Rule Token Expr
  this =
    do s <- location
       symbol "("
       keyword "this"
       t <- (ref <|> expr)
       keyword "as"
       ty <- type
       symbol ")"
       e <- location
       pure (This (newFC s e) t ty)

  that =
    do s <- location
       symbol "("
       keyword "that"
       t <- (ref <|> expr)
       keyword "as"
       ty <- type
       symbol ")"
       e <- location
       pure (That (newFC s e) t ty)

  funAnon : Rule Token Expr
  funAnon =
    do s <- location
       symbol "("
       keyword "fun"
       args <- commaSepBy1 (do a <- location
                               n <- name
                               symbol ":"
                               ty <- type
                               b <- location
                               pure (newFC a b, n, ty))
       suchThat
       body <- expr
       symbol ")"
       e <- location
       pure (foldr (\(fc,n,ty),acc => Fun fc n ty acc) body (forget args))


  cond : Rule Token Expr
  cond =
    do s <- location
       keyword "if"
       c <- (ref <|> expr)
       keyword "then"
       t <- expr
       keyword "else"
       f <- expr
       e <- location
       pure (Cond (newFC s e) c t f)

  let_ : Rule Token Expr
  let_ =
    do s <- location
       keyword "let"
       rec <- optional (keyword "rec")
       n <- name
       symbol ":"
       ty <- type
       assign
       v <- expr
       keyword "in"
       b <- expr
       e <- location
       pure (Let (newFC s e) n ty (isJust rec) v b)

  app : Rule Token Expr
  app =
    do s <- location
       symbol "("
       keyword "apply"
       f <- expr
       a <- expr
       symbol ")"
       e <- location
       pure (App (newFC s e) f a)

  unit : Rule Token Expr
  unit = gives "unit" TheUnit

  ascription : Rule Token Expr
  ascription =
    do s <- location
       symbol "("
       keyword "the"
       ty <- type
       v  <- expr
       symbol ")"
       e <- location
       pure (The (newFC s e) ty v)

  match_pair : Rule Token Expr
  match_pair
    = do s <- location
         keyword "match"
         c <- expr
         keyword "as"
         symbol "{"
         symbol "("
         a <- name
         symbol ","
         b <- name
         symbol ")"
         suchThat
         r <- expr
         symbol "}"
         e <- location
         pure (MatchPair (newFC s e) c a b r)

  match_list : Rule Token Expr
  match_list
    = do s <- location
         keyword "match"
         c <- expr
         keyword "as"
         symbol "{"
         keyword "empty"
         suchThat
         emp <- expr
         symbol "|"
         keyword "extend"
         h <- name
         t <- name
         suchThat
         rest <- expr
         symbol "}"
         e <- location
         pure (MatchList (newFC s e) c emp h t rest)

  match_sum : Rule Token Expr
  match_sum
    = do s <- location
         keyword "match"
         c <- expr
         keyword "as"
         symbol "{"
         keyword "this"
         l <- name
         suchThat
         bl <- expr
         symbol "|"
         keyword "that"
         r <- name
         suchThat
         br <- expr
         symbol "}"
         e <- location
         pure (MatchSum (newFC s e) c l bl r br)

  expr : Rule Token Expr
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

main_ : Rule Token Prog
main_ =
  do s <- location
     keyword "main"
     assign
     v <- expr
     e <- location
     pure (Main (newFC s e) v)


decl : Rule Token (FileContext, String, Ty, Bool, Expr)
decl =
  do s <- location
     keyword "def"
     rec <- optional (keyword "rec")
     n <- name
     symbol ":"
     t <- type
     assign
     v <- expr
     e <- location
     pure (newFC s e, n, t, isJust rec, v)

olaf : Rule Token Prog
olaf =
  do ds <- many decl
     m <- main_
     eoi
     pure (foldr (\(fc, n, ty, rec, v),acc =>
                      Decl fc n ty rec v acc)
                 m ds)

namespace Olaf

  namespace Expression
    export
    fromString : (str : String)
                     -> (Either (Run.ParseError Token) Expr)
    fromString str
      = parseString Olaf.lexer expr str

  namespace Programme
    export
    fromFile : (fname : String)
                     -> IO (Either (Run.ParseError Token) Prog)
    fromFile fname
      = case !(parseFile Olaf.lexer olaf fname) of
          Left err  => pure (Left err)
          Right ast => pure (Right (map (setSource fname) ast))

-- [ EOF ]
