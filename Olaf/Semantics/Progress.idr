module Olaf.Semantics.Progress

import Decidable.Equality

import public Toolkit.Data.List.DeBruijn

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
import Olaf.Semantics.Reductions

%default total

public export
data Progress : (term : Term Nil type)
                     -> Type
  where
    Done : forall mty
         . {term : Term Nil mty}
        -> (val  : Value term)
                -> Progress term

    Step : {this, that : Term Nil type}
        -> (step       : Redux this that)
                      -> Progress this

export
progress : {ty   : Ty}
        -> (term : Term Nil ty)
                -> Progress term

progress (Var _) impossible

-- [ Builtins ]
progress (B x)
  = Done B

progress {ty} (BOp kind l r) with (kind)
  progress {ty = TyNat} (BOp kind l r) | (NOp PLUS) with (progress l)
    progress {ty = TyNat} (BOp kind (B v) r) | (NOp PLUS) | (Done B) with (progress r)
      progress {ty = TyNat} (BOp kind (B l) (B r)) | (NOp PLUS) | (Done B) | (Done B)
        = Step (ReduceBOp B B ReduceAdd)
      progress {ty = TyNat} (BOp kind (B l) r) | (NOp PLUS) | (Done B) | (Step step)
        = Step (SimplifyBOpRight B step)
    progress {ty = TyNat} (BOp kind l r) | (NOp PLUS) | (Step step)
      = Step (SimplifyBOpLeft step)

  progress {ty = TyNat} (BOp kind l r) | (NOp SUB) with (progress l)
    progress {ty = TyNat} (BOp kind (B l) r) | (NOp SUB) | (Done B) with (progress r)
      progress {ty = TyNat} (BOp kind (B l) (B r)) | (NOp SUB) | (Done B) | (Done B)
        = Step (ReduceBOp B B ReduceSub)
      progress {ty = TyNat} (BOp kind (B l) r) | (NOp SUB) | (Done B) | (Step step)
        = Step (SimplifyBOpRight B step)
    progress {ty = TyNat} (BOp kind l r) | (NOp SUB) | (Step step)
      = Step (SimplifyBOpLeft step)

  progress {ty = TyBool} (BOp kind l r) | (BOp AND) with (progress l)
    progress {ty = TyBool} (BOp kind (B v) r) | (BOp AND) | (Done B) with (progress r)
      progress {ty = TyBool} (BOp kind (B l) (B r)) | (BOp AND) | (Done B) | (Done B)
        = Step (ReduceBOp B B ReduceAnd)
      progress {ty = TyBool} (BOp kind (B l) r) | (BOp AND) | (Done B) | (Step step)
        = Step (SimplifyBOpRight B step)
    progress {ty = TyBool} (BOp kind l r) | (BOp AND) | (Step step)
      = Step (SimplifyBOpLeft step)

  progress {ty = TyBool} (BOp kind l r) | (BOp OR) with (progress l)
    progress {ty = TyBool} (BOp kind (B l) r) | (BOp OR) | (Done B) with (progress r)
      progress {ty = TyBool} (BOp kind (B l) (B r)) | (BOp OR) | (Done B) | (Done B)
        = Step (ReduceBOp B B ReduceIor)
      progress {ty = TyBool} (BOp kind (B l) r) | (BOp OR) | (Done B) | (Step step)
        = Step (SimplifyBOpRight B step)
    progress {ty = TyBool} (BOp kind l r) | (BOp OR) | (Step step)
      = Step (SimplifyBOpLeft step)

  progress {ty = TyBool} (BOp kind l r) | (BOp XOR) with (progress l)
    progress {ty = TyBool} (BOp kind (B v) r) | (BOp XOR) | (Done B) with (progress r)
      progress {ty = TyBool} (BOp kind (B l) (B r)) | (BOp XOR) | (Done B) | (Done B)
        = Step (ReduceBOp B B ReduceXor)
      progress {ty = TyBool} (BOp kind (B v) r) | (BOp XOR) | (Done B) | (Step step)
        = Step (SimplifyBOpRight B step)
    progress {ty = TyBool} (BOp kind l r) | (BOp XOR) | (Step step)
      = Step (SimplifyBOpLeft step)

  progress {ty = TyBool} (BOp kind l r) | NCmp with (progress l)
    progress {ty = TyBool} (BOp kind (B l) r) | NCmp | (Done B) with (progress r)
      progress {ty = TyBool} (BOp kind (B l) (B r)) | NCmp | (Done B) | (Done B)
        = Step (ReduceBOp B B ReduceLT)
      progress {ty = TyBool} (BOp kind (B l) r) | NCmp | (Done B) | (Step step)
        = Step (SimplifyBOpRight B step)
    progress {ty = TyBool} (BOp kind l r) | NCmp | (Step step)
      = Step (SimplifyBOpLeft step)

progress {ty} (UOp kind e) with (kind)
  progress {ty = (Return op)} (UOp kind e) | (SOp op) with (progress e)
    progress {ty = (Return SIZE)} (UOp kind (B v)) | (SOp SIZE) | (Done B)
      = Step (ReduceUOp B ReduceSize)

    progress {ty = (Return PACK)} (UOp kind e) | (SOp PACK) | (Done val) with (pack e val)
      progress {ty = (Return PACK)} (UOp kind e) | (SOp PACK) | (Done val) | (MkDPair fst snd)
        = Step (ReduceUOp val (ReducePack val snd))

    progress {ty = (Return UNPACK)} (UOp kind (B v)) | (SOp UNPACK) | (Done B) with (PackUn.unpack (unpack v))
      progress {ty = (Return UNPACK)} (UOp kind (B v)) | (SOp UNPACK) | (Done B) | (MkDPair fst snd)
        = Step (ReduceUOp B (ReducePackUn snd))

    progress {ty = (Return op)} (UOp kind e) | (SOp op) | (Step step)
      = Step (SimplifyUOp step)

  progress {ty = (Return op)} (UOp kind e) | (COp op) with (progress e)
    progress {ty = (Return TOSTR)} (UOp kind (B v)) | (COp TOSTR) | (Done B)
      = Step (ReduceUOp B ReduceStr)

    progress {ty = (Return ORD)} (UOp kind (B v)) | (COp ORD) | (Done B)
      = Step (ReduceUOp B ReduceOrd)

    progress {ty = (Return CHAR)} (UOp kind (B v)) | (COp CHAR) | (Done B)
      = Step (ReduceUOp B ReduceChar)

    progress {ty = (Return op)} (UOp kind e) | (COp op) | (Step step)
      = Step (SimplifyUOp step)

  progress {ty = TyBool} (UOp kind e) | BNot with (progress e)
    progress {ty = TyBool} (UOp kind (B v)) | BNot | (Done B)
      = Step (ReduceUOp B ReduceBNot)

    progress {ty = TyBool} (UOp kind e) | BNot | (Step step)
      = Step (SimplifyUOp step)

-- [ Data Structures]

-- -- [ Lists ]
progress Empty
  = Done Empty

progress (Extend head tail) with (progress head)
  progress (Extend head tail) | (Done h) with (progress tail)
    progress (Extend head tail) | (Done h) | (Done t)
      = Done (Extend h t)
    progress (Extend head tail) | (Done h) | (Step step)
      = Step (ReduceListTail step)
  progress (Extend head tail) | (Step step)
    = Step (ReduceListHead step)

progress (MatchList what empty extend) with (progress what)
  progress (MatchList Empty empty extend) | (Done Empty)
    = Step (ReduceMatchListNil)
  progress (MatchList (Extend h t) empty extend) | (Done (Extend x y))
    = Step (ReduceMatchListCons)

  progress (MatchList what empty extend) | (Step step)
    = Step (SimplifyMatchList step)

-- -- [ Pairs/Products ]
progress (Pair l r) with (progress l)
  progress (Pair l r) | (Done val) with (progress r)
    progress (Pair l r) | (Done vl) | (Done vr)
      = Done (Pair vl vr)
    progress (Pair l r) | (Done vl) | (Step step)
      = Step (SimplifyPairRight step)

  progress (Pair l r) | (Step step)
    = Step (SimplifyPairLeft step)

progress (MatchPair pair cases) with (progress pair)
  progress (MatchPair (Pair f s) cases) | (Done (Pair x y))
    = Step (ReduceMatchPair)
  progress (MatchPair pair cases) | (Step step)
    = Step (SimplifyMatchPair step)

-- -- [ Variants/Sums]
progress (This e) with (progress e)
  progress (This e) | (Done val)
    = Done (This val)
  progress (This e) | (Step step)
    = Step (SimplifyThis step)

progress (That e) with (progress e)
  progress (That e) | (Done val)
    = Done (That val)
  progress (That e) | (Step step)
    = Step (SimplifyThat step)

progress (MatchSum what this that) with (progress what)
  progress (MatchSum (This t) this that) | (Done (This x))
    = Step (ReduceMatchSumThis)
  progress (MatchSum (That t) this that) | (Done (That x))
    = Step (ReduceMatchSumThat)
  progress (MatchSum what this that) | (Step step)
    = Step (SimplifyMatchSum step)

-- [ Control Structures ]
progress (Cond test tt ff) with (progress test)
  progress (Cond (B False) tt ff) | (Done B)
    = Step (ReduceCondFalse)
  progress (Cond (B True) tt ff) | (Done B)
    = Step (ReduceCondTrue)
  progress (Cond test tt ff) | (Step step)
    = Step (SimplifyCond step)

progress (Rec this)
  = Step ReduceRec

-- [ Bindings ]
progress (Let this body)
  = Step ReduceLet

-- [ STLC ]
progress (Fun a body)
  = Done Fun

progress (App f a) with (progress f)
  progress (App f a) | (Done vf) with (progress a)
    progress (App (Fun x body) a) | (Done Fun) | (Done val)
      = Step (ReduceFuncApp {body=body} val)

    progress (App f a) | (Done vf) | (Step step)
      = Step (SimplifyFuncAppVar vf step)

  progress (App f a) | (Step step)
    = Step (SimplifyFuncAppFunc step)

-- [ Unit ]
progress U
  = Done U

-- [ Ascriptions]
progress (The ty term)
  = Step ReduceThe

-- [ EOF ]
