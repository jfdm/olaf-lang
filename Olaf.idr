module Olaf

import public Data.Nat
import public Data.String
import public Data.List
import public Data.List.Elem
import public Data.Bool.Xor

import public Olaf.Core
import public Olaf.Interpreter

namespace API
  export
  nat : Nat -> Term ctxt TyNat
  nat = B

  export
  bool : Bool -> Term ctxt TyBool
  bool = B

  export
  str : String -> Term ctxt TyString
  str = B

  export
  char : Char -> Term ctxt TyChar
  char = B

  export
  not : (e : Term ctxt TyBool)
          -> Term ctxt TyBool
  not = UOp BNot

  export
  size : (e : Term ctxt TyString)
           -> Term ctxt TyNat
  size = UOp (SOp SIZE)

  export
  pack : (e : Term ctxt (TyList TyChar))
           -> Term ctxt TyString
  pack = UOp (SOp PACK)

  export
  unpack : (e : Term ctxt TyString)
             -> Term ctxt (TyList TyChar)
  unpack = UOp (SOp UNPACK)

  export
  toString : (e : Term ctxt TyChar)
               -> Term ctxt TyString
  toString = UOp (COp TOSTR)

  export
  toNat : (e : Term ctxt TyChar)
            -> Term ctxt TyNat
  toNat = UOp (COp ORD)

  export
  toChar : (e : Term ctxt TyNat)
             -> Term ctxt TyChar
  toChar = UOp (COp CHAR)

  export
  lessThan : (l,r : Term ctxt TyNat)
                 -> Term ctxt TyBool
  lessThan = BOp NCmp

  export
  and, or, xor : (l,r : Term ctxt TyBool)
                     -> Term ctxt TyBool
  and = BOp (BOp AND)
  or  = BOp (BOp OR)
  xor = BOp (BOp XOR)

  export
  add, sub : (l,r : Term ctxt TyNat)
                 -> Term ctxt TyNat
  add = BOp (NOp PLUS)
  sub = BOp (NOp SUB)

  export
  empty : (ty : Ty) -> Term ctxt (TyList ty)
  empty _ = Empty

  export
  extend : Term ctxt type
        -> Term ctxt (TyList type)
        -> Term ctxt (TyList type)
  extend = Extend

  namespace List
    export
    match : (what   : Term ctxt (TyList a))
         -> (empty  : Term ctxt b)
         -> (extend : Term ((ctxt += a) += (TyList a)) b)
                   -> Term ctxt b
    match = MatchList

  export
  tuple : (l : Term ctxt a)
        -> (r : Term ctxt b)
             -> Term ctxt (TyProduct a b)
  tuple l r = Pair l r

  namespace Pair
    export
    match : (pair  : Term ctxt (TyProduct a b))
         -> (cases : Term ((ctxt += a) += b) c)
                  -> Term ctxt c
    match = MatchPair

  export
  isThis : (e : Term ctxt a)
             -> Term ctxt (TySum a b)
  isThis = This

  export
  isThat : (e : Term ctxt b)
             -> Term ctxt (TySum a b)
  isThat = That

  namespace Variant
    export
    match : (what : Term ctxt (TySum a b))
         -> (this : Term (ctxt += a) c)
         -> (that : Term (ctxt += b) c)
                 -> Term ctxt c
    match = MatchSum

  export
  cond : (test  : Term ctxt TyBool)
      -> (tt,ff : Term ctxt b)
               -> Term ctxt b
  cond = Cond

  export
  rec : (this : Term (ctxt += a) a)
             -> Term ctxt a
  rec = Rec

-- [ EOF ]
