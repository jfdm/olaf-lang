module Olaf.Terms

import Decidable.Equality

import public Toolkit.Data.List.DeBruijn

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem

import Olaf.Types
import public Olaf.Types.Operators

%default total

namespace Context
  public export
  Context : Type
  Context = List Ty


public export
data Term : Context -> Ty -> Type where
  B : {b : Builtin} -> PrimTy b -> Term ctxt (TyBuiltin b)

  BOp : {arg,ret : Ty}
     -> (kind : BinOp arg ret)
     -> (l,r  : Term ctxt arg)
             -> Term ctxt ret

  UOp : {arg,ret : Ty}
     -> (kind : UnOp arg ret)
     -> (e    : Term ctxt arg)
             -> Term ctxt ret

  -- [ Data ]
  Empty : Term ctxt (TyList a)

  Extend : (head : Term ctxt a)
        -> (tail : Term ctxt (TyList a))
                -> Term ctxt (TyList a)

  MatchList : {a,b : Ty}
           -> (what   : Term ctxt (TyList a))
           -> (empty  : Term ctxt b)
           -> (extend : Term ((ctxt += a) += (TyList a)) b)
                     -> Term ctxt b

  Pair : (l : Term ctxt a)
      -> (r : Term ctxt b)
           -> Term ctxt (TyProduct a b)

  MatchPair : {a,b,c : Ty}
           -> (pair  : Term ctxt (TyProduct a b))
           -> (cases : Term ((ctxt += a) += b) c)
                    -> Term ctxt c

  This : (e : Term ctxt a)
           -> Term ctxt (TySum a b)

  That : (e : Term ctxt b)
           -> Term ctxt (TySum a b)

  MatchSum : {a,b,c : Ty}
          -> (what : Term ctxt (TySum a b))
          -> (this : Term (ctxt += a) c)
          -> (that : Term (ctxt += b) c)
                  -> Term ctxt c

  -- [ Control Structures ]

  Cond : (test  : Term ctxt TyBool)
      -> (tt,ff : Term ctxt b)
               -> Term ctxt b

  Rec : (this : Term (ctxt += a) a)
             -> Term ctxt a

  -- [ Bindings ]
  Let : {a,b : Ty}
     -> (this : Term ctxt a)
     -> (body : Term (ctxt += a) b)
             -> Term ctxt b

  -- [ STLC ]
  Var : {type : Ty} -> Elem type ctxt -> Term ctxt type

  Fun : (a : Ty)
     -> (body : Term (ctxt += a) b)
             -> Term ctxt (TyFunc a b)

  App : {x,y : Ty}
     -> (f : Term ctxt (TyFunc x y))
     -> (a : Term ctxt x)
          -> Term ctxt y

  -- [ Unit ]

  U  : Term ctxt TyUnit

  -- [ Ascriptions ]
  The : (type : Ty)
     -> (term : Term ctxt type)
             -> Term ctxt type

-- [ EOF ]
