module Olaf.Semantics.Evaluation

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem
import Data.Bool.Xor
import Data.Fuel

import Toolkit.Data.Nat

import public Toolkit.Data.List.DeBruijn




import Olaf.Types

import Olaf.Terms

import Olaf.Terms.Renaming
import Olaf.Terms.Substitution

import Olaf.Values

import public Olaf.Semantics.Reductions.Pack
import public Olaf.Semantics.Reductions.Builtins
import public Olaf.Semantics.Reductions
import Olaf.Semantics.Progress

%default total

public export
data Finished : (term : Term ctxt type)
                     -> Type
  where
    Normalised : {term : Term ctxt type}
                      -> Value term
                      -> Finished term
    OOF : Finished term

public export
data Evaluate : (term : Term Nil type) -> Type where
  RunEval : {this, that : Term Nil type}
         -> (steps      : Inf (Reduces this that))
         -> (result     : Finished that)
                       -> Evaluate this


evaluate : {type : Ty}
        -> (fuel : Fuel)
        -> (term : Term Nil type)
                -> Evaluate term
evaluate Dry term = RunEval Refl OOF
evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Done value) = RunEval Refl (Normalised value)
  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (RunEval steps result)
      = RunEval (Trans step steps) result

public export
data EvalResult : (term : Term Nil type) -> Type where
  R : (that : Term Nil type)
   -> (val  : Value that)
   -> (steps : Reduces this that)
            -> EvalResult this

export covering
run : {type : Ty}
   -> (this : Term Nil type)
           -> Maybe (EvalResult this)
run this with (evaluate forever this)
  run this | (RunEval steps (Normalised {term} x))
    = Just (R term x steps)
  run this | (RunEval steps OOF) = Nothing

-- [ EOF ]
