module Olaf.Syntax.Milly.Pretty

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
ty (TyBuiltin Str) = pretty "String"
ty (TyBuiltin Chr) = pretty "Char"

ty (TyList x)
  = parens (hsep [pretty "List", ty x])

ty (TyProduct x y)
  = parens (hsep [pretty "Pair", ty x, ty y])

ty (TySum x y)
  = parens (hsep [pretty "Sum", ty x, ty y])

ty (TyFunc x y)
  = parens (hsep [ty x, pretty "->", ty y])
ty TyUnit = pretty "Unit"

unOp : UnOp a r -> Doc ()
unOp (SOp SIZE) = pretty "size"
unOp (SOp PACK) = pretty "pack"
unOp (SOp UNPACK) = pretty "unpack"
unOp (COp TOSTR) = pretty "toString"
unOp (COp ORD) = pretty "ord"
unOp (COp CHAR) = pretty "char"
unOp BNot = pretty "not"

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

olaf Empty
  = pretty "empty"

olaf (Extend head tail)
  = group (parens (hsep [olaf head, olaf tail]))

olaf (MatchList what empty extend)
  = parens (pretty "match" <++> (align $ vsep [ olaf what <++> pretty "with"
                                              , pipe <++> pretty "empty => " <+> (olaf empty)
                                              , pipe <++> pretty "extend => " <+> (olaf extend)]))

olaf (Pair l r)
  = parens (hsep [olaf l <+> comma, olaf r])

olaf (MatchPair pair cases)
  = parens (pretty "match" <++> (align $ vsep [ olaf pair <++> pretty "with"
                                              , pipe <++> pretty "(,) => " <+> (olaf cases)]))

olaf (This e)
  = parens (hsep [pretty "this", olaf e])
olaf (That e)
  = parens (hsep [pretty "that", olaf e])

olaf (MatchSum what this that)
  = parens (pretty "match"
             <++> (align $ vsep [olaf what <++> pretty "with"
                                , pipe <++> pretty "this => " <+> (olaf this)
                                , pipe <++> pretty "that =>" <+> (olaf that)]))

olaf (Cond test tt ff)
  = parens (pretty "if" <++> (align $ vsep [ olaf test
                                           , pretty "then" <++> olaf tt
                                           , pretty "else" <++> olaf ff]))

olaf (Rec this)
  = parens (hsep [pretty "rec", olaf this])

olaf (Let this body)
  = parens (pretty "let" <++> (align $ vsep [ (olaf this) <++> equals
                                            , (olaf body)
                                            ]))


olaf (Var x)
  = parens (hsep [pretty "var", elem x])

olaf (Fun a body)
  = parens (pretty "fun" <++> align (vsep [ty a, olaf body]))

olaf (App f a)
  = parens (pretty "apply" <++> align (vsep [olaf f, olaf a]))

olaf U
  = pretty "Unit"

olaf (The type term)
  = parens (hsep [pretty "the", ty type, olaf term])

namespace Olaf
  namespace Milly
    export
    pretty : Term ctxt type -> Doc ()
    pretty = olaf

    export
    prettyTypes : Ty -> Doc ()
    prettyTypes = ty
-- [ EOF ]
