module Olaf.Terms.Substitution

import Toolkit.Data.List.DeBruijn

import Olaf.Types
import Olaf.Terms

import Olaf.Terms.Renaming


public export
Substitute Ty Term where

  subst f (B x)
    = B x

  subst f (BOp (NOp x) l r) = BOp (NOp x) (General.subst f l) (General.subst f r)
  subst f (BOp (BOp x) l r) = BOp (BOp x) (General.subst f l) (General.subst f r)
  subst f (BOp NCmp    l r) = BOp NCmp    (General.subst f l) (General.subst f r)

  subst f (UOp BNot         e) = UOp BNot         (General.subst f e)
  subst f (UOp (SOp SIZE)   e) = UOp (SOp SIZE)   (General.subst f e)
  subst f (UOp (SOp PACK)   e) = UOp (SOp PACK)   (General.subst f e)
  subst f (UOp (SOp UNPACK) e) = UOp (SOp UNPACK) (General.subst f e)
  subst f (UOp (COp TOSTR)  e) = UOp (COp TOSTR)  (General.subst f e)
  subst f (UOp (COp ORD)    e) = UOp (COp ORD)    (General.subst f e)
  subst f (UOp (COp CHAR)   e) = UOp (COp CHAR)   (General.subst f e)

  subst f Empty
    = Empty

  subst f (Extend head tail)
    = Extend (General.subst f head)
             (General.subst f tail)

  subst f (MatchList what empty extend)
    = MatchList (General.subst f what)
                (General.subst f empty)
                (General.subst (weakens (weakens f) extend)

  subst f (Pair l r)
    = Pair (General.subst f l)
           (General.subst f r)

  subst f (MatchPair pair cases)
    = MatchPair (General.subst f pair)
                (General.subst ((weakens . weakens) f) cases)

  subst f (This e)
    = This (General.subst f e)

  subst f (That e)
    = That (General.subst f e)

  subst f (MatchSum what this that)
    = MatchSum (General.subst f what)
               (General.subst (weakens f) this)
               (General.subst (weakens f) that)

  subst f (Cond test tt ff)
    = Cond (General.subst f test)
           (General.subst f tt)
           (General.subst f ff)

  subst f (Rec this)
    = Rec (General.subst (weakens f) this)

  subst f (Let this body)
    = Let (General.subst f this)
          (General.subst (weakens f) body)

  subst f (Var x)
    = (f x)

  subst f (Fun a body)
    = Fun a (General.subst (weakens f) body)

  subst f (App x a)
    = App (General.subst f x) (General.subst f a)

  subst f U
    = U

  subst f (The ty term)
    = The ty (General.subst f term)

-- [ EOF ]
