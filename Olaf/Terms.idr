module Olaf.Terms

import Decidable.Equality

import public Toolkit.Data.List.DeBruijn

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem

import Olaf.Types

%default total

namespace Context
  public export
  Context : Type
  Context = List Ty

namespace Operations

  public export
  data NatArithOp = PLUS | SUB

  public export
  data BoolArithOp = AND | OR | XOR

  public export
  data BinOp = NOp NatArithOp
             | BOp BoolArithOp
             | NCmp

  namespace TyBin
    public export
    Operand : BinOp -> Ty
    Operand (NOp x) = TyNat
    Operand (BOp x) = TyBool
    Operand NCmp    = TyNat

    public export
    Return : BinOp -> Ty
    Return (NOp x) = TyNat
    Return (BOp x) = TyBool
    Return NCmp    = TyBool

  public export
  data StringOp = SIZE | PACK | UNPACK

  public export
  data CharOp = TOSTR | ORD | CHAR

  public export
  data UnOp = BNot
            | SOp StringOp
            | COp CharOp

  namespace TyUn
    public export
    Operand : UnOp -> Ty
    Operand BNot         = TyBool
    Operand (SOp SIZE)   = TyString
    Operand (SOp PACK)   = TyList TyChar
    Operand (SOp UNPACK) = TyString
    Operand (COp TOSTR)  = TyChar
    Operand (COp ORD)    = TyChar
    Operand (COp CHAR)   = TyNat

    public export
    Return : UnOp -> Ty
    Return BNot         = TyBool
    Return (SOp SIZE)   = TyNat
    Return (SOp PACK)   = TyString
    Return (SOp UNPACK) = TyList TyChar
    Return (COp TOSTR)  = TyString
    Return (COp ORD)    = TyNat
    Return (COp CHAR)   = TyChar

namespace Terms


  public export
  data Term : Context -> Ty -> Type where
    B : {b : Builtin} -> PrimTy b -> Term ctxt (TyBuiltin b)

    BOp : (kind : BinOp)
       -> (l,r  : Term ctxt (TyBin.Operand kind))
               -> Term ctxt (TyBin.Return  kind)

    UOp : (kind : UnOp)
       -> (e    : Term ctxt (TyUn.Operand kind))
               -> Term ctxt (TyUn.Return kind)

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

namespace Prog
  public export
  data Prog : Context -> Ty -> Type where
    Main : Term ctxt type -> Prog ctxt type
    Decl : Term ctxt type
        -> Prog (ctxt += type) p
        -> Prog  ctxt          p


-- [ EOF ]
