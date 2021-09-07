module Olaf.Values

import Decidable.Equality

import public Toolkit.Data.List.DeBruijn

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem

import Olaf.Types
import Olaf.Terms

%default total


public export
data Value : Term ctxt type -> Type where
  -- [ Prims ]
  B : Value (B v)

  -- [ Data ]
  Empty : Value Empty

  Extend : Value h -> Value t -> Value (Extend h t)

  Pair : Value f -> Value s -> Value (Pair f s)

  This : Value t -> Value (This t)
  That : Value t -> Value (That t)

  U : Value U

  Fun : {body : Term (ctxt += type) btype}
             -> Value (Fun type body)


-- [ EOF ]
