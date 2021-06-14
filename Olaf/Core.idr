module Olaf.Core

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem
import Data.Bool.Xor

%default total

namespace Types

  public export
  data Builtin = Nat | Bool | Str | Chr

  namespace Ty
    public export
    data Ty = TyBuiltin Builtin
            | TyList Ty | TyProduct Ty Ty | TySum Ty Ty
            | TyFunc Ty Ty
            | TyUnit

  public export
  TyNat, TyBool, TyString, TyChar : Ty
  TyNat  = TyBuiltin Nat
  TyBool = TyBuiltin Bool
  TyString = TyBuiltin Str
  TyChar   = TyBuiltin Chr

  public export
  PrimTy : Builtin -> Type
  PrimTy Nat = Nat
  PrimTy Bool = Bool
  PrimTy Str = String
  PrimTy Chr = Char

namespace Context
  public export
  Context : Type
  Context = List Ty

  infixr 6 +=

  public export
  (+=) : Context -> Ty -> Context
  (+=) = flip (::)

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

    MatchList : (what   : Term ctxt (TyList a))
             -> (empty  : Term ctxt b)
             -> (extend : Term ((ctxt += a) += (TyList a)) b)
                       -> Term ctxt b

    Pair : (l : Term ctxt a)
        -> (r : Term ctxt b)
             -> Term ctxt (TyProduct a b)

    MatchPair : (pair  : Term ctxt (TyProduct a b))
             -> (cases : Term ((ctxt += a) += b) c)
                      -> Term ctxt c

    This : (e : Term ctxt a)
             -> Term ctxt (TySum a b)

    That : (e : Term ctxt b)
             -> Term ctxt (TySum a b)

    MatchSum : (what : Term ctxt (TySum a b))
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
    Let : (this : Term ctxt a)
       -> (body : Term (ctxt += a) b)
               -> Term ctxt b

    -- [ STLC ]
    Var : Elem type ctxt -> Term ctxt type

    Fun : (body : Term (ctxt += a) b)
               -> Term ctxt (TyFunc a b)

    App : (f : Term ctxt (TyFunc x y))
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
