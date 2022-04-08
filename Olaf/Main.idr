module Olaf.Main

import System
import System.File

import Data.List1
import Data.String
import Data.Either

import Toolkit.Data.Location

import Olaf
import Olaf.AST
import Olaf.TypeCheck
import Olaf.Types
import Olaf.Terms
import Olaf.Values

import Olaf.Semantics.Evaluation

import Olaf.Syntax.PythonEsque

Show a => Show (ParseFailure a) where
  show err
    = trim $ unlines [show (location err), (error err)]

Show a => Show (Run.ParseError a) where
  show (FError err)
    = trim $ unlines ["File Error: "
                     , show err]
  show (PError err)
    = trim $ unlines (forget (map show err))

  show (LError (MkLexFail l i))
    = trim $ unlines [show l, show i]

Show Builtin where
  show Nat = "Nat"
  show Bool = "Bool"
  show Str = "String"
  show Chr = "Char"

Show Ty where
  show (TyBuiltin x) = show x
  show (TyList x) = "(List " <+> show x <+> ")"
  show (TyProduct x y) = "(Pair " <+> show x <+> " "<+> show y <+> ")"
  show (TySum x y) = "(Sum " <+> show x <+> " "<+> show y <+> ")"
  show (TyFunc x y) = "(" <+> show x <+> " -> "<+> show y <+> ")"
  show TyUnit = "Unit"

sexpr : String -> String -> String
sexpr t e = unwords ["(" <+> t, e <+> ")"]

namespace Expr
  namespace BOp
    export
    showKind : BinOp tyA tyR -> String
    showKind (NOp PLUS) = "+"
    showKind (NOp SUB) = "-"
    showKind (BOp AND) = "&&"
    showKind (BOp OR) = "||"
    showKind (BOp XOR) = "^"
    showKind NCmp = "<"

  namespace UOp
    export
    showKind : UnOp tyA tyR -> String
    showKind BNot = "not"
    showKind (SOp SIZE) = "size"
    showKind (SOp PACK) = "pack"
    showKind (SOp UNPACK) = "unpack"
    showKind (COp TOSTR) = "toString"
    showKind (COp ORD) = "toNat"
    showKind (COp CHAR) = "toChar"

  show : AST a -> String
  show (Ref x y) = show y

  show (S x y) = show y
  show (B x y) = show y
  show (C x y) = show y
  show (N x k) = show k

  show (UOp fc k expr) = sexpr (showKind k) (show expr)

  show (BOp fc k l r) = sexpr (showKind k) (unwords [show l, show r])

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
  showTerm' : (term : Term ctxt ty) -> String
  showTerm' (B {b = Nat} x)  = show x
  showTerm' (B {b = Bool} x) = show x
  showTerm' (B {b = Str} x)  = show x
  showTerm' (B {b = Chr} x)  = show x

  showTerm' (BOp kind l r)
    = unwords ["(" <+> showTerm' l, showKind kind, showTerm' r <+> ")"]

  showTerm' (UOp kind e)
    = unwords ["(" <+> showKind kind, showTerm' e <+> ")"]

  showTerm' Empty
    = "[]"
  showTerm' (Extend head tail)
    = unwords ["(" <+> showTerm' head, "::", showTerm' tail <+>")"]
  showTerm' (MatchList what empty extend)
    = unwords ["(match", showTerm' what, "{", showTerm' empty, "|", showTerm' extend <+> "})"]


  showTerm' (Pair l r)
    = unwords ["(" <+> showTerm' l <+> ",", showTerm' r <+> ")"]
  showTerm' (MatchPair pair cases)
    = unwords ["(match", showTerm' pair, "{", showTerm' cases <+> "})"]

  showTerm' (This e)
    = unwords ["(this" <+> showTerm' e <+> ")"]
  showTerm' (That e)
    = unwords ["(that" <+> showTerm' e <+> ")"]
  showTerm' (MatchSum what this that)
    = unwords ["(match", showTerm' what, "{", showTerm' this, "|", showTerm' that <+> "})"]

  showTerm' (Cond test tt ff)
    = unwords ["(f", showTerm' test, "{", showTerm' tt, "} else {", showTerm' tt <+> "})"]

  showTerm' (Rec this)
    = unwords ["(rec", showTerm' this <+> ")"]

  showTerm' (Let this body)
    = unwords ["(let", showTerm' this, "in {", showTerm' body <+> "})"]

  showTerm' (Var x)
      = unwords ["(var", showElem x <+> ")"]
    where
      toNat : Elem ty xs -> Nat
      toNat Here = Z
      toNat (There x) = S (toNat x)

      showElem : Elem ty xs -> String
      showElem =  (show . toNat)

  showTerm' (Fun a body)
    = unwords ["(\\" <+> show a, "->", "{" <+> showTerm' body <+> "})"]
  showTerm' (App f a)
    = unwords ["(" <+> showTerm' f, "$", showTerm' a <+> ")"]

  showTerm' U
    = "unit"

  showTerm' (The ty term)
    = unwords ["the", show ty, showTerm' term]

namespace Eval

  showRedux : Redux a b -> String
  showRedux (SimplifyBOpLeft x) = "Simplify Left Operand by " ++ showRedux x
  showRedux (SimplifyBOpRight x y) = "Simplify Right Operand by " ++ showRedux y
  showRedux (ReduceBOp vl vr x) = "Reduce Binary Operation"
  showRedux (SimplifyUOp x) = "Simplify Unary Operation by " ++ showRedux x
  showRedux (ReduceUOp val prf) = "Reduce Unary Operand"
  showRedux (ReduceListHead x) = "Reduce List Head by " ++ showRedux x
  showRedux (ReduceListTail x) = "Reduce List Tail by " ++ showRedux x
  showRedux (SimplifyMatchList x) = "Simplify Match List by " ++ showRedux x
  showRedux ReduceMatchListNil = "Reduce Match List Nil"
  showRedux ReduceMatchListCons = "Reduce Match List Cons"
  showRedux (SimplifyPairLeft x)  = "Simplify Left by " ++ showRedux x
  showRedux (SimplifyPairRight x) = "Simplify Right by " ++ showRedux x
  showRedux (SimplifyMatchPair x) = "Simplify Match Pair by " ++ showRedux x
  showRedux ReduceMatchPair = "Reduce Match Pair"
  showRedux (SimplifyThis x) = "Simplify This by " ++ showRedux x
  showRedux (SimplifyThat x) = "Simplify That by " ++ showRedux x
  showRedux (SimplifyMatchSum x) = "Simplify Match Sum by" ++ showRedux x
  showRedux ReduceMatchSumThis = "Reduce Match Sum This"
  showRedux ReduceMatchSumThat = "Reduce Match Sum That"
  showRedux (SimplifyCond x) = "Simplify Conditional by " ++ showRedux x
  showRedux ReduceCondTrue  = "Reduce Conditional True"
  showRedux ReduceCondFalse = "Reduce Conditional False"
  showRedux ReduceRec = "Reduce Recursion"
  showRedux ReduceLet = "Reduce Let Binding"
  showRedux (SimplifyFuncAppFunc func) = "Simplify Application Function"
  showRedux (SimplifyFuncAppVar value var) = "Simplify Application Variable by " ++ showRedux var
  showRedux (ReduceFuncApp x) = "Reduce Application"
  showRedux ReduceThe = "Reduce Ascription"

  showReduces : {a,b : Term Nil ty} -> Reduces a b -> List String
  showReduces {a = a} {b = a} Refl
    = [showTerm' a]
  showReduces {a = a} {b = b} (Trans x y)
    = showTerm' a :: ("= " <+> showRedux x) :: showReduces y


  export
  showEvalRes : {term : Term Nil ty} -> (res : EvalResult term) -> String
  showEvalRes {term = term} (R that val steps)
    = trim $ unlines (showReduces steps)


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

       Right ast <- Olaf.PythonEsque.Programme.fromFile y
          | Left err => do printLn err
                           exitFailure

       putStrLn "-- LOG : Parsed"

       -- printLn ast

       Right (R Nil type term) <- Closed.build ast
          | Left err => do printLn err
                           exitFailure

       putStrLn "-- LOG : Checked"

       putStrLn "-- LOG : Running"
       case run term of
         Nothing => do printLn "Ran out of fuel"
                       exitFailure
         Just res --(R t v steps)
           => do putStrLn (showEvalRes res)
                 putStrLn "-- LOG : Finished"
                 exitSuccess


-- [ EOF ]
