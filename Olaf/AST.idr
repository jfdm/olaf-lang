module Olaf.AST

import Data.String

import Data.List1

import Toolkit.Data.Location

import Olaf

%default total


namespace Olaf
  public export
  data AST a = Ref a String
             | S a String
             | B a Bool
             | C a Char
             | N a Nat
             | UOp a (UnOp tyA tyR) (AST a)
             | BOp a (BinOp tyA tyR) (AST a) (AST a)

             | MatchPair a (AST a) String String (AST a)

             | MatchList a (AST a) (AST a) String String (AST a)

             | MatchSum a (AST a) String (AST a) String (AST a)

             | Empty a Ty
             | Extend a (AST a) (AST a)
             | Pair a (AST a) (AST a)
             | This a (AST a) Ty
             | That a (AST a) Ty

             | Cond a (AST a) (AST a) (AST a)
             | Let a String Ty Bool (AST a) (AST a)
             | Fun a String Ty (AST a)
             | App a (AST a) (AST a)

             | TheUnit a
             | The a Ty (AST a)

public export
Expr : Type
Expr = AST FileContext



map : (a -> b) -> AST a -> AST b
map f (Ref x y) = Ref (f x) y
map f (S x y) = S (f x) y
map f (B x y) = B (f x) y
map f (C x y) = C (f x) y
map f (N x k) = N (f x) k
map f (UOp x y z) = UOp (f x) y (map f z)
map f (BOp x y z w) = BOp (f x) y (map f z) (map f w)

map f (MatchPair fc p x y body)
  = MatchPair (f fc) (map f p) x y (map f body)

map f (MatchList fc l n h t body)
  = MatchList (f fc) (map f l) (map f n) h t (map f body)

map f (MatchSum fc sum this bthis that bthat)
  = MatchSum (f fc) (map f sum) this (map f bthis) that (map f bthat)

map f (Empty x ty) = Empty (f x) ty
map f (Extend x y z) = Extend (f x) (map f y) (map f z)
map f (Pair x y z) = Pair (f x) (map f y) (map f z)
map f (This x y ty) = This (f x) (map f y) ty
map f (That x y ty) = This (f x) (map f y) ty
map f (Cond x y z w) = Cond (f x) (map f y) (map f z) (map f w)
map f (Let x y t b z w) = Let (f x) y t b (map f z) (map f w)

map f (Fun x y z w) = Fun (f x) y z (map f w)
map f (App x y z) = App (f x) (map f y) (map f z)
map f (TheUnit x) = TheUnit (f x)
map f (The x y z) = The (f x) y (map f z)

export
Functor AST where
  map f a = map f a

export
getFC : AST FileContext -> FileContext
getFC (Ref x y)                 = x
getFC (S x y)                   = x
getFC (B x y)                   = x
getFC (C x y)                   = x
getFC (N x k)                   = x
getFC (UOp x y z)               = x
getFC (BOp x y z w)             = x
getFC (MatchPair x p f s b)     = x
getFC (MatchList x l n h t b)   = x
getFC (MatchSum  x s t tb y yb) = x
getFC (Empty x ty)              = x
getFC (Extend x y z)            = x
getFC (Pair x y z)              = x
getFC (This x y ty)             = x
getFC (That x y ty)             = x
getFC (Cond x y z w)            = x
getFC (Let x y t b z w)         = x
getFC (Fun x y z w )            = x
getFC (App x y z)               = x
getFC (TheUnit x)               = x
getFC (The x y z)               = x

-- [ EOF ]
