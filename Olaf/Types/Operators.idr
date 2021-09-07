module Olaf.Types.Operators

import Olaf.Types

%default total

namespace Binary
  public export
  data NatArithOp = PLUS | SUB

  public export
  data BoolArithOp = AND | OR | XOR

  public export
  data BinOp : Ty -> Ty -> Type where
    NOp : (op : NatArithOp)
             -> BinOp TyNat TyNat

    BOp : (op : BoolArithOp)
             -> BinOp TyBool TyBool

    NCmp : BinOp TyNat TyBool

namespace Unary
  public export
  data StringOp = SIZE | PACK | UNPACK

  public export
  data CharOp = TOSTR | ORD | CHAR

  namespace Char
    public export
    Operand : CharOp -> Ty
    Operand TOSTR  = TyChar
    Operand ORD    = TyChar
    Operand CHAR   = TyNat

    public export
    Return : CharOp -> Ty
    Return TOSTR  = TyString
    Return ORD    = TyNat
    Return CHAR   = TyChar

  namespace String
    public export
    Operand : StringOp -> Ty
    Operand SIZE   = TyString
    Operand PACK   = TyList TyChar
    Operand UNPACK = TyString

    public export
    Return : StringOp -> Ty
    Return SIZE   = TyNat
    Return PACK   = TyString
    Return UNPACK = TyList TyChar

  public export
  data UnOp : Ty -> Ty -> Type where
    SOp : (op : StringOp)
             -> UnOp (Operand op)
                     (Return  op)

    COp : (op : CharOp)
             -> UnOp (Operand op)
                     (Return  op)

    BNot : UnOp TyBool TyBool

-- [ EOF ]
