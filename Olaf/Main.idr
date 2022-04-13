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

import Olaf.Syntax.Milly
import Olaf.Syntax.Milly.Pretty

import Olaf.Syntax.Lispy
import Olaf.Syntax.Lispy.Pretty

import Olaf.Syntax.STLC
import Olaf.Syntax.STLC.Pretty

record Syntax where
  constructor S
  parseFile : String -> IO (Either (ParseError Token) Expr)
  prettify  : {type : Ty} -> Term Nil type -> Doc ()
  prettyTypes : Ty -> Doc ()

showErr : Syntax -> Error -> String
showErr s (Err x y)
  = trim $ unlines ["Error Occurred"
                   , show x
                   , (showErr s y)]
showErr _ ExpSum = "Sum Expected"
showErr _ ExpFunc = "Function Expected"
showErr _ ExpProduct = "Pair Expected"
showErr _ ExpList = "List Expected"
showErr _ (NotName x) = "Not a name: " <+> show x

showErr s (MMatch x y)
  = trim $ unlines [ "Type Mismatch"
                   , "Expected:"
                   , "\t" <+> show ((prettyTypes s) x)
                   , "Given:"
                   , "\t" <+> show ((prettyTypes s) y)
                   ]

STLC : Syntax
STLC = S Olaf.STLC.Programme.fromFile
         Olaf.STLC.pretty
         Olaf.STLC.prettyTypes

Milly : Syntax
Milly = S Olaf.Milly.Programme.fromFile
          Olaf.Milly.pretty
          Olaf.Milly.prettyTypes

Lispy : Syntax
Lispy = S Olaf.Lispy.Programme.fromFile
          Olaf.Lispy.pretty
          Olaf.Lispy.prettyTypes

namespace PrettyComps
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

  wrap : {type : Ty} -> Syntax -> Term Nil type -> Doc ()
  wrap {type} s tm
    = vcat [ Doc.pretty "```"
           , (prettify s) tm
           , Doc.pretty "```"
           ]


  showSteps : {ty : Ty} -> {a,b : Term Nil ty} -> Syntax -> Reduces a b -> List (Doc ())
  showSteps {a = a} {b = a} s Refl
    = [wrap s a]

  showSteps {a = a} {b = b} s (Trans x y)
    = wrap s a :: (pretty $ "### " <+> showRedux x) :: showSteps s y

  export
  prettyComputation : Syntax
                   -> {ty : Ty}
                   -> {term : Term Nil ty}
                   -> (res  : EvalResult term) -> IO ()
  prettyComputation s {term = term} (R that val steps)
    = printLn $ vcat (showSteps s steps)

parseArgs : List String -> IO (Pair String Syntax)
parseArgs (exe::"lispy"::y::Nil)
  = pure (y, Lispy)

parseArgs (exe::"milly"::y::Nil)
  = pure (y, Milly)

parseArgs (exe::"stlc"::y::Nil)
  = pure (y, STLC)
parseArgs _
  = do putStrLn "<lispy/milly/stlc> <filename>"
       exitSuccess


parseFile : Syntax -> String -> IO Expr
parseFile s fname
  = do case !((Syntax.parseFile s) fname) of
         Right ast => pure ast
         Left  err => do printLn err
                         exitFailure

main : IO ()
main
  = do args <- getArgs
       (fname,syn) <- parseArgs args

       ast <- parseFile syn fname

       putStrLn "## LOG : Parsed"

       -- printLn ast

       Right (type ** term) <- Closed.build ast
          | Left err => do putStrLn $ showErr syn err
                           exitFailure

       putStrLn "## LOG : Checked"

       putStrLn "## LOG : Running"
       case run term of
         Nothing => do printLn "Ran out of fuel"
                       exitFailure
         Just res
           => do prettyComputation syn res
                 putStrLn "-- LOG : Finished"
                 exitSuccess


-- [ EOF ]
