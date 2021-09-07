module Olaf.Syntax.Parser

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.String
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

namespace Olaf
  public export
  Rule : Type -> Type
  Rule = Rule () Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty () Token

namespace API

  export
  eoi : RuleEmpty ()
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False

  export
  symbol : String -> Rule ()
  symbol str
    = terminal ("Expected Symbol '" ++ str ++ "'")
               (\x => case x of
                             Symbol s => if s == str then Just ()
                                                     else Nothing
                             _ => Nothing)

  export
  arrow : Rule ()
  arrow = symbol "->"

  export
  assign : Rule ()
  assign = symbol ":="

  export
  suchThat : Rule ()
  suchThat = symbol "=>"

  export
  keyword : String -> Rule ()
  keyword str
    = terminal ("Expected Keyword '" ++ str ++ "'")
                 (\x => case x of
                             Keyword s => if s == str then Just ()
                                                      else Nothing
                             _ => Nothing)

  export
  natLit : Rule Nat
  natLit = terminal "Expected nat literal"
               (\x => case x of
                           LitNat i => Just i
                           _ => Nothing)

  export
  strLit : Rule String
  strLit = terminal "Expected string literal"
               (\x => case x of
                           LitStr i => Just i
                           _ => Nothing)

  export
  charLit : Rule Char
  charLit = terminal "Expected string literal"
               (\x => case x of
                           LitChr i =>
                             case unpack i of
                               Nil => Just '\0000'
                               [x] => Just x
                               _   => Nothing
                           _ => Nothing)


  export
  identifier : Rule String
  identifier
    = terminal "Expected Identifier"
               (\x => case x of
                                  ID str => Just str
                                  _ => Nothing)

  export
  name : Rule String
  name = identifier

  export
  parens : Inf (Rule a)
        -> Rule a
  parens p = between (symbol "(") (symbol ")") p

  export
  arrowSepBy1 : Rule a -> Rule (List1 a)
  arrowSepBy1 = sepBy1 arrow

  export
  commaSepBy1 : Rule a -> Rule (List1 a)
  commaSepBy1 = sepBy1 (symbol ",")

  export
  gives : String -> (FileContext -> a) -> Rule a
  gives s ctor
    = do a <- Toolkit.location
         keyword s
         b <- Toolkit.location
         pure (ctor (newFC a b))


  export
  inserts : Rule a -> (FileContext -> a -> b) -> Rule b
  inserts value ctor
    = do a <- Toolkit.location
         v <- value
         b <- Toolkit.location
         pure (ctor (newFC a b) v)

ref : Rule Expr
ref = inserts name    Ref

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
       args <- commaSepBy1 (do a <- Toolkit.location
                               n <- name
                               symbol ":"
                               ty <- type
                               b <- Toolkit.location
                               pure (newFC a b, n, ty))
       suchThat
       body <- expr
       symbol ")"
       e <- Toolkit.location
       pure (foldr (\(fc,n,ty),acc => Fun fc n ty acc) body (forget args))


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
  let_ =
    do s <- Toolkit.location
       keyword "let"
       rec <- optional (keyword "rec")
       n <- name
       symbol ":"
       ty <- type
       assign
       v <- expr
       keyword "in"
       b <- expr
       e <- Toolkit.location
       pure (Let (newFC s e) n ty (isJust rec) v b)

  app : Rule Expr
  app =
    do s <- Toolkit.location
       symbol "("
       keyword "apply"
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
         e <- Toolkit.location
         pure (MatchPair (newFC s e) c a b r)

  match_list : Rule Expr
  match_list
    = do s <- Toolkit.location
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
         e <- Toolkit.location
         pure (MatchList (newFC s e) c emp h t rest)

  match_sum : Rule Expr
  match_sum
    = do s <- Toolkit.location
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
     keyword "main"
     assign
     v <- expr
     e <- Toolkit.location
     pure v


decl : Rule (FileContext, String, Ty, Bool, Expr)
decl =
  do s <- Toolkit.location
     keyword "def"
     rec <- optional (keyword "rec")
     n <- name
     symbol ":"
     t <- type
     assign
     v <- expr
     e <- Toolkit.location
     pure (newFC s e, n, t, isJust rec, v)

olaf : Rule Expr
olaf =
  do ds <- many decl
     m <- main_
     eoi
     pure (foldr (\(fc, n, ty, rec, v),acc =>
                      Let fc n ty rec v acc)
                 m ds)

namespace Olaf

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
