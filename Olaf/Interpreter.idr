module Olaf.Interpreter

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem
import Data.Bool.Xor

import Olaf.Core

%default total

namespace Type
  public export
  interp : Ty -> Type
  interp (TyBuiltin Nat) = Nat
  interp (TyBuiltin Bool) = Bool
  interp (TyBuiltin Str) = String
  interp (TyBuiltin Chr) = Char
  interp (TyList x) = List (interp x)
  interp (TyProduct x y) = Pair (interp x) (interp y)
  interp (TySum x y) = Either (interp x) (interp y)
  interp (TyFunc x y) = interp x -> interp y
  interp TyUnit = Unit

namespace Env
  public export
  data Env : Context -> Type where
    Nil : Env Nil
    (::) : (head : Type.interp type)
        -> (tail : Env  types)
                -> Env (types += type)

  export
  get : (env : Env ctxt)
     -> (idx : Elem type ctxt)
            -> Type.interp type
  get (x :: y) Here = x
  get (x :: xs) (There prf) = get xs prf

namespace Expr
  export
  interp : (env : Env ctxt)
        -> (tm  : Term ctxt type)
               -> Type.interp type

  interp env (B {b = Nat} y) = y
  interp env (B {b = Bool} y) = y
  interp env (B {b = Str} y) = y
  interp env (B {b = Chr} y) = y

  interp env (BOp (NOp PLUS) l r)
    = plus (interp env l) (interp env r)

  interp env (BOp (NOp SUB) l r)
    = minus (interp env l) (interp env r)

  interp env (BOp (BOp AND) l r)
    = (&&) (interp env l) (interp env r)

  interp env (BOp (BOp OR) l r)
    = (||) (interp env l) (interp env r)

  interp env (BOp (BOp XOR) l r)
    = xor (interp env l) (interp env r)

  interp env (BOp NCmp l r)
    = (<) (interp env l) (interp env r)

  interp env (UOp BNot e)
    = not (interp env e)

  interp env (UOp (SOp SIZE) e)
    = length (interp env e)

  interp env (UOp (SOp PACK) e)
    = pack (interp env e)

  interp env (UOp (SOp UNPACK) e)
    = unpack (interp env e)

  interp env (UOp (COp TOSTR) e)
    = cast (interp env e)

  interp env (UOp (COp ORD) e)
    = fromInteger (cast {to=Integer} (ord (interp env e)))

  interp env (UOp (COp CHAR) e)
    = chr (cast {to=Int} (interp env e))

  interp env Empty = Nil
  interp env (Extend head tail) = interp env head :: interp env tail

  interp env (MatchList what empty extend) with (interp env what)
    interp env (MatchList what empty extend) | []
      = interp env empty
    interp env (MatchList what empty extend) | (y :: xs)
      = interp (xs :: (y :: env)) extend

  interp env (Pair l r) = MkPair (interp env l) (interp env r)

  interp env (MatchPair pair cases) with (interp env pair)
    interp env (MatchPair pair cases) | (y, z)
      = interp (z::(y::env)) cases

  interp env (This e) = Left (interp env e)
  interp env (That e) = Right (interp env e)

  interp env (MatchSum what this that) with (interp env what)
    interp env (MatchSum what this that) | (Left y)
      = interp (y::env) this

    interp env (MatchSum what this that) | (Right y)
      = interp (y::env) that

  interp env (Cond test tt ff) with (interp env test)
    interp env (Cond test tt ff) | False = interp env ff
    interp env (Cond test tt ff) | True = interp env tt

  interp env (Rec this) = interp (interp env (Rec this)::env) this


  interp env (Let this body)
    = interp ((interp env this)::env) body

  interp env (Var idx)
    = get env idx

  interp env (Fun body) = \a => interp (a::env) body

  interp env (App f a)
    = (interp env f) (interp env a)

  interp env U = ()

  interp env (The type term) = the (interp type) (interp env term)

namespace Programme
  export
  interp : (env  : Env ctxt)
        -> (prog : Prog ctxt type)
                -> Type.interp type
  interp env (Main expr) = interp env expr

  interp env (Decl decl prog)
    = Programme.interp (Expr.interp env decl::env) prog

interp : (prog : Prog Nil type)
              -> Type.interp type
interp = Programme.interp Nil

-- [ EOF ]
