module Olaf.Semantics.Reductions.Builtins

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

%default total

namespace BinOps
  public export
  and : Bool -> Bool -> Bool
  and l r = (&&) l r

  public export
  ior : Bool -> Bool -> Bool
  ior l r = (||) l r

  public export
  data Redux : (kind : BinOp arg ret)
            -> (l,r  : Term Nil arg)
            -> Value l
            -> Value r
            -> (res  : Term Nil ret)
                    -> Type
    where
      ReduceAdd : Redux (NOp PLUS) (B l) (B r) B B (B (plus  l r))
      ReduceSub : Redux (NOp SUB)  (B l) (B r) B B (B (minus l r))

      ReduceAnd : Redux (BOp AND)  (B l) (B r) B B (B (and l r))
      ReduceIor : Redux (BOp OR )  (B l) (B r) B B (B (ior l r))
      ReduceXor : Redux (BOp XOR)  (B l) (B r) B B (B (xor l r))

      ReduceLT : Redux NCmp (B x) (B y) B B (B (x < y))


namespace UnOps
  public export
  data Redux : (kind : UnOp arg ret)
            -> (a    : Term Nil arg)
            -> (val  : Value a)
            -> (res  : Term Nil ret)
                    -> Type
    where
      ReduceBNot : Redux BNot (B b) B (B (not b))

      ReduceSize : Redux (SOp SIZE) (B str) B (B (length str))

      ReducePack : (prf : Value cs)
                -> (op  : Pack cs prf str)
                -> Redux (SOp PACK) cs prf str

      ReducePackUn : (op : PackUn (unpack str) cs)
                        -> Redux (SOp UNPACK) (B str) B cs

      ReduceStr : Redux (COp TOSTR) (B c) B (B (cast c))

      ReduceOrd : Redux (COp ORD) (B c) B (B (toNat (ord c)))

      ReduceChar : Redux (COp CHAR) (B n) B (B (chr (cast {to=Int} n)))


-- [ EOF ]
