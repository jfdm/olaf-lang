module Olaf.Syntax.PythonEsque.Parser

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

import Olaf.Syntax.PythonEsque.Lexer

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

-- [ EOF ]
