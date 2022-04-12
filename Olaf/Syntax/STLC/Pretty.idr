module Olaf.Syntax.STLC.Pretty

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.String
import Data.Maybe

import public Text.PrettyPrint.Prettyprinter

import Olaf

%default total

ty : Ty -> Doc ()
ty (TyBuiltin Nat) = pretty "Nat"
ty (TyBuiltin Bool) = pretty "Bool"
ty (TyFunc x y)
  = parens (hsep [ty x, pretty "->", ty y])

ty _ = emptyDoc

unOp : UnOp a r -> Doc ()
unOp BNot = pretty "not"
unOp _ = emptyDoc

binOp : BinOp a r -> Doc ()
binOp (NOp PLUS) = pretty "plus"
binOp (NOp SUB) = pretty "sub"
binOp (BOp AND) = pretty "and"
binOp (BOp OR) = pretty "or"
binOp (BOp XOR) = pretty "xor"
binOp NCmp = pretty "lessThan"

elem : Elem typ xs -> Doc ()
elem = (pretty . toNat)
  where
    toNat : Elem y ys -> Nat
    toNat Here = Z
    toNat (There x) = S (toNat x)


olaf : Term ctxt type -> Doc ()
olaf (B {b = Nat} x)
  = pretty x
olaf (B {b = Bool} x)
  = pretty x
olaf (B {b = Str} x)
  = pretty x
olaf (B {b = Chr} x)
  = pretty x

olaf (BOp kind l r)
  = group $ parens (hsep [binOp kind, olaf l, olaf r])

olaf (UOp kind e)
  = group $ parens (hsep [unOp kind, olaf e])

olaf (Cond test tt ff)
  = parens (pretty "if" <++> (align $ vsep [ olaf test
                                           , pretty "then" <++> olaf tt
                                           , pretty "else" <++> olaf ff]))

olaf (Rec this)
  = parens (hsep [pretty "rec", olaf this])

olaf (Let this body)
  = parens (pretty "let" <++> (align $ vsep [ (olaf this)
                                            , (olaf body)
                                            ]))

olaf (Var x)
  = parens (hsep [pretty "var", elem x])

olaf (Fun a body)
  = parens (pretty "fun" <++> align (vsep [ty a, olaf body]))

olaf (App f a)
  = parens (pretty "apply" <++> align (vsep [olaf f, olaf a]))

olaf _
  = emptyDoc

namespace Olaf
  namespace STLC
    export
    pretty : Term ctxt type -> Doc ()
    pretty = olaf

    export
    prettyTypes : Ty -> Doc ()
    prettyTypes = ty
-- [ EOF ]
