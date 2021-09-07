module Olaf.Semantics.Reductions.Pack

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

%default total

namespace Pack

  public export
  data Pack : (cs  : Term Nil (TyList TyChar))
           -> (prf : Value cs)
           -> (res : Term Nil TyString)
                  -> Type

    where
      Empty : Pack Empty Empty (B "")
      Extend : Pack cs prf (B str)
            -> Pack (Extend (B c) cs)
                    (Extend B  prf)
                    (B (strCons c str))

  export
  pack : (cs  : Term Nil (TyList TyChar))
      -> (prf : Value cs)
             -> DPair (Term Nil TyString) (Pack cs prf)
  pack cs prf with (prf)
    pack Empty prf | Empty = (_ ** Empty)
    pack (Extend h t) prf | (Extend x y) with (x)
      pack (Extend (B v) t) prf | (Extend x y) | B with (pack t y)
        pack (Extend (B v) t) prf | (Extend x y) | B | (MkDPair (B rest) snd) = (B _ ** (Extend snd))


namespace PackUn
  public export
  data PackUn : (cs  : List Char)
             -> (res : Term Nil (TyList TyChar))
                    -> Type
    where
      Empty : PackUn Nil Empty
      Extend : PackUn cs                    cs'
            -> PackUn (c::cs) (Extend (B c) cs')

  export
  unpack : (cs  : List Char)
               -> DPair (Term Nil (TyList TyChar)) (PackUn cs)
  unpack [] = MkDPair Empty Empty
  unpack (x :: xs) with (unpack xs)
    unpack (x :: xs) | (MkDPair fst snd) = MkDPair (Extend (B x) fst) (Extend snd)

-- [ EOF ]
