module Olaf.Terms.Renaming

import Toolkit.DeBruijn.Renaming

import Olaf.Types
import Olaf.Terms

%default total

public export
Rename Ty Term where
  var = Var

  rename f (B x) = B x

  rename f (BOp (NOp x) l r) = BOp (NOp x) (rename f l) (rename f r)
  rename f (BOp (BOp x) l r) = BOp (BOp x) (rename f l) (rename f r)
  rename f (BOp NCmp    l r) = BOp NCmp    (rename f l) (rename f r)

  rename f (UOp BNot         e) = UOp BNot         (rename f e)
  rename f (UOp (SOp SIZE)   e) = UOp (SOp SIZE)   (rename f e)
  rename f (UOp (SOp PACK)   e) = UOp (SOp PACK)   (rename f e)
  rename f (UOp (SOp UNPACK) e) = UOp (SOp UNPACK) (rename f e)
  rename f (UOp (COp TOSTR)  e) = UOp (COp TOSTR)  (rename f e)
  rename f (UOp (COp ORD)    e) = UOp (COp ORD)    (rename f e)
  rename f (UOp (COp CHAR)   e) = UOp (COp CHAR)   (rename f e)

  rename f Empty
    = Empty

  rename f (Extend head tail)
    = Extend (rename f head)
             (rename f tail)

  rename f (MatchList what empty extend)
    = MatchList (rename f what)
                (rename f empty)
                (rename ((weaken . weaken) f) extend)

  rename f (Pair l r)
    = Pair (rename f l)
           (rename f r)

  rename f (MatchPair pair cases)
    = MatchPair (rename f pair)
                (rename ((weaken . weaken) f) cases)

  rename f (This e)
    = This (rename f e)

  rename f (That e)
    = That (rename f e)

  rename f (MatchSum what this that)
    = MatchSum (rename f what)
               (rename (weaken f) this)
               (rename (weaken f) that)

  rename f (Cond test tt ff)
    = Cond (rename f test)
           (rename f tt)
           (rename f ff)

  rename f (Rec this)
    = Rec (rename (weaken f) this)

  rename f (Let this body)
    = Let (rename f this)
          (rename (weaken f) body)

  rename f (Var x)
    = Var (f x)

  rename f (Fun a body)
    = Fun a (rename (weaken f) body)

  rename f (App x a)
    = App (rename f x) (rename f a)

  rename f U
    = U

  rename f (The ty term)
    = The ty (rename f term)

-- [ EOF ]
