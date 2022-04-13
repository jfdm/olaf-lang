module Olaf.Semantics.Reductions

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem
import Data.Bool.Xor

import Toolkit.Data.Nat

import Olaf.Types

import Olaf.Terms

import Olaf.Terms.Renaming
import Olaf.Terms.Substitution

import Olaf.Values

import Olaf.Semantics.Reductions.Pack
import Olaf.Semantics.Reductions.Builtins

%default total

public export
data Redux : (this,that : Term ctxt type)
                       -> Type
  where
    -- [ Ops ]
    -- -- [ Binary Ops]
    SimplifyBOpLeft : Redux this that
                   -> Redux (BOp kind this right)
                            (BOp kind that right)

    SimplifyBOpRight : Value left
                    -> Redux this that
                    -> Redux (BOp kind left this)
                             (BOp kind left that)

    ReduceBOp : {kind : BinOp arg ret}
             -> {l,r : Term Nil arg}
             -> {res : Term Nil ret}
             -> (vl : Value l)
             -> (vr : Value r)
             -> Redux kind l r vl vr res
             -> Redux (BOp kind l r)
                      res

    -- -- [ Unary Ops]
    SimplifyUOp : Redux this that
               -> Redux (UOp kind this)
                        (UOp kind that)

    ReduceUOp  : {kind : UnOp arg ret}
              -> {a   : Term Nil arg}
              -> {res : Term Nil ret}
              -> (val : Value a)
              -> (prf : Redux kind a val res)
                     -> Redux (UOp kind a)
                              res


    -- [ Data Structures]
    -- -- [ Lists ]
    ReduceListHead : Redux this that
                  -> Redux (Extend this rest)
                           (Extend that rest)

    ReduceListTail : Redux this that
                  -> Redux (Extend v this)
                           (Extend v that)

    SimplifyMatchList : Redux this that
                     -> Redux (MatchList this nil cons)
                              (MatchList that nil cons)

    ReduceMatchListNil : Redux (MatchList Empty nil cons)
                               nil

    ReduceMatchListCons : {a,b : Ty}
                       -> {nil : Term ctxt b}
                       -> {cons : Term ((ctxt += a) += (TyList a)) b}
                       -> {h    : Term ctxt a}
                       -> {t    : Term ctxt (TyList a)}
                       -> Redux (MatchList (Extend h t) nil cons)
                                (Double.subst h t cons)

    -- -- [ Products ]
    SimplifyPairLeft : Redux this that
                    -> Redux (Pair this r) (Pair that r)

    SimplifyPairRight : Redux this that
                     -> Redux (Pair l this) (Pair l that)

    SimplifyMatchPair : Redux this that
                     -> Redux (MatchPair this cases)
                              (MatchPair that cases)

    ReduceMatchPair : Redux (MatchPair (Pair f s) cases)
                            (Double.subst f s cases)

    -- -- [ Sums ]
    SimplifyThis : Redux this that
                -> Redux (This this) (This that)

    SimplifyThat : Redux this that
                -> Redux (That this) (That that)


    SimplifyMatchSum : Redux this that
                    -> Redux (MatchSum this whenThis whenThat)
                             (MatchSum that whenThis whenThat)

    ReduceMatchSumThis : Redux (MatchSum (This this) whenThis whenThat)
                               (subst this whenThis)

    ReduceMatchSumThat : Redux (MatchSum (That that) whenThis whenThat)
                               (subst that whenThat)

    -- [ Control Structures ]
    SimplifyCond : Redux this that
                -> Redux (Cond this tt ff)
                         (Cond that tt ff)

    ReduceCondTrue : Redux (Cond (B True) tt ff)
                           tt

    ReduceCondFalse : Redux (Cond (B False) tt ff)
                            ff

    ReduceRec : {term : Term (ctxt += type) type}
                     -> Redux (Rec term)
                              (subst (Rec term) term)

    -- [ Bindings ]
    ReduceLet : Redux (Let this body)
                      (subst this body)

    -- [ STLC ]
    SimplifyFuncAppFunc : (func : Redux this that)
                               -> Redux (App this var)
                                        (App that var)

    SimplifyFuncAppVar : {this, that : Term ctxt type}
                      -> {func       : Term ctxt (TyFunc type return)}
                      -> (value      : Value func)
                      -> (var        : Redux this that)
                                    -> Redux (App func this)
                                             (App func that)

    ReduceFuncApp : {ctxt : List Ty}
                 -> {type : Ty}
                 -> {body : Term (ctxt += type) return}
                 -> {var  : Term  ctxt    type}
                 -> Value var
                          -> Redux (App (Fun type body) var)
                                   (Single.subst var body)

    -- [ Ascriptions ]
    ReduceThe : Redux (The ty term)
                      term

public export
data Reduces : (this : Term ctxt type)
            -> (that : Term ctxt type)
            -> Type
  where
    Refl  : {this : Term ctxt type}
                 -> Reduces this this

    Trans : {this, that, end : Term ctxt type}
         -> Redux this that
         -> Reduces that end
         -> Reduces this end

-- [ EOF ]
