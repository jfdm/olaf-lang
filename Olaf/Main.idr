module Olaf.Main

import System
import System.File

import Data.List1
import Data.String
import Data.Either

import Toolkit.Data.Location

import Olaf
import Olaf.Syntax
import Olaf.Types
import Olaf.Terms
import Olaf.Values

import Olaf.Semantics.Evaluation


export
Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

export
Show a => Show (Run.ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map show err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]

export
Show Builtin where
  show Nat = "Nat"
  show Bool = "Bool"
  show Str = "String"
  show Chr = "Char"

export
Show Ty where
  show (TyBuiltin x) = show x
  show (TyList x) = "(List " <+> show x <+> ")"
  show (TyProduct x y) = "(Pair " <+> show x <+> " "<+> show y <+> ")"
  show (TySum x y) = "(Sum " <+> show x <+> " "<+> show y <+> ")"
  show (TyFunc x y) = "(" <+> show x <+> "->"<+> show y <+> ")"
  show TyUnit = "Unit"

sexpr : String -> String -> String
sexpr t e = unwords ["(" <+> t, e <+> ")"]

namespace Expr

  show : AST a -> String
  show (Ref x y) = show y

  show (S x y) = show y
  show (B x y) = show y
  show (C x y) = show y
  show (N x k) = show k

  show (UOp fc k expr) = sexpr (showKind k) (show expr)
    where
      showKind : UnOp tyA tyR -> String
      showKind BNot = "not"
      showKind (SOp SIZE) = "size"
      showKind (SOp PACK) = "pack"
      showKind (SOp UNPACK) = "unpack"
      showKind (COp TOSTR) = "toString"
      showKind (COp ORD) = "toNat"
      showKind (COp CHAR) = "toChar"

  show (BOp fc k l r) = sexpr (showKind k) (unwords [show l, show r])
    where
      showKind : BinOp tyA tyR -> String
      showKind (NOp PLUS) = "add"
      showKind (NOp SUB) = "sub"
      showKind (BOp AND) = "and"
      showKind (BOp OR) = "or"
      showKind (BOp XOR) = "xor"
      showKind NCmp = "lt"

  show (MatchPair fc c l r body)
    = sexpr "match" (unwords [ show c, "as"
                             , "{ (", show l, ",", show r, ") =>"
                             , show body, "}"])

  show (MatchList fc c emp h t rest)
    = sexpr "match" (unwords [ show c, "as"
                             , "{ empty =>", show emp
                             , "| extend", show h, show t, "=>", show rest
                             , "}"])


  show (MatchSum fc c l lb r rb)
    = sexpr "match" (unwords [ show c, "as"
                             , "{ this", show l, "=>", show lb
                             , "| that", show r, "=>", show rb
                             , "}"])


  show (Empty fc ty) = "empty" <+> "[" <+> show ty <+> "]"
  show (Extend fc h t) = sexpr "extend" (unwords [show h, show t])
  show (Pair fc a b) = sexpr "tuple" (unwords [show a, show b])
  show (This fc t ty) = sexpr "this" (unwords [show t, "as", show ty])
  show (That fc t ty) = sexpr "that" (unwords [show t, "as", show ty])
  show (Cond fc c t f) = sexpr "cond" (unwords [show c, show t, show f])
  show (Let fc n ty rec value body)
    = sexpr ("let" <+> if rec then "rec" else "")
            (unwords [n, ":", show ty, ":=", show value, "in", show body])
  show (Fun fc n ty body)
    = sexpr "fun" (unwords [n, ":", show ty, "=>", show body])
  show (App fc f a) = sexpr "app" (unwords [show f, show a])
  show (TheUnit fc) = "unit"
  show (The x y z) = unwords ["(the", show y, show z <+>")"]

  export
  Show (AST a) where
    show = Expr.show

namespace Term
  export
  showTerm : (term : Term Nil ty) -> Value term -> String
  showTerm (B {b = Nat} v) B  = show v
  showTerm (B {b = Bool} v) B = show v
  showTerm (B {b = Str} v) B  = show v
  showTerm (B {b = Chr} v) B  = show v

  showTerm Empty Empty = "[]"
  showTerm (Extend h t) (Extend x y)
    = concat [showTerm h x, "::", showTerm t y]

  showTerm (Pair f s) (Pair x y)
    = concat ["(", showTerm f x, ",", showTerm s y, ")"]

  showTerm (This t) (This x)
    = concat ["(This ", showTerm t x,")"]

  showTerm (That t) (That x)
    = concat ["(That ", showTerm t x,")"]

  showTerm U U = "U"

  showTerm (Fun type body) Fun
    = concat ["(fun...",")"]

export
Show Error where
  show (Err x y)
    = trim $ unlines ["Error Occurred"
                     , show x
                     , show y]
  show ExpSum = "Sum Expected"
  show ExpFunc = "Function Expected"
  show ExpProduct = "Pair Expected"
  show ExpList = "List Expected"
  show (NotName x) = "Not a name: " <+> show x

  show (MMatch x y)
    = trim $ unlines [ "Type Mismatch"
                     , "Expected:"
                     , "\t" <+> show x
                     , "Given:"
                     , "\t" <+> show y
                     ]

main : IO ()
main
  = do (x::y::Nil) <- getArgs
          | _ => do putStrLn "Just one file please"
                    exitSuccess

       Right ast <- Olaf.Programme.fromFile y
          | Left err => do printLn err
                           exitFailure

       putStrLn "Parsed"

       printLn ast

       Right (R Nil type term) <- Closed.build ast
          | Left err => do printLn err
                           exitFailure

       putStrLn "Checked"

       putStrLn "Running"
       case run term of
         Nothing => do printLn "Ran out of fuel"
                       exitFailure
         Just (R t v steps)
           => do putStrLn (showTerm t v)
                 putStrLn "\n"
                 exitSuccess


-- [ EOF ]
