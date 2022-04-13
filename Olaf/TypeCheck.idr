module Olaf.TypeCheck

import Decidable.Equality

import Data.Vect
import Data.Nat
import Data.List

import Data.List.Views
import Data.List1
import Data.String
import Data.Maybe

import Text.Lexer
import Text.Parser

import Toolkit.Decidable.Informative
import Toolkit.Data.Location

import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Toolkit.DeBruijn.Context

import Olaf

import Olaf.AST

%default total

public export
data Error : Type where
  Err : FileContext -> Error -> Error
  ExpSum : Error
  ExpFunc : Error
  ExpProduct : Error
  ExpList : Error
  NotName : String -> Error
  MMatch : (x,y : Ty) -> Error

Result : List Ty -> Type
Result = Result Ty Term

View : (p   : Ty -> Type)
    -> {types : List Ty}
    -> (res : Result types)
           -> Type
View = View Ty Term

public export
Build : Type -> Type
Build = Either Error

isBuiltin : (fc : FileContext)
         -> (b  : Builtin)
         -> {types : List Ty}
         -> (r  : Result types)
               -> Build (Term types (TyBuiltin b))
isBuiltin fc b r with (view (isBuiltin b) r)
  isBuiltin fc b (R ctxt (TyBuiltin b) term) | (V M)
    = Right term
  isBuiltin fc b (R ctxt type term) | (V F)
    = Left (Err fc (MMatch (TyBuiltin b) type))

isListOf : (fc : FileContext)
        -> (ty : Ty)
         -> {types : List Ty}
        -> (r  : Result types)
              -> Build (Term types (TyList ty))
isListOf fc ty r with (view (isListOf ty) r)
  isListOf fc ty (R ctxt (TyList ty) term) | (V M)
    = Right term
  isListOf fc ty (R ctxt type term) | (V F)
    = Left (Err fc (MMatch (TyList ty) type))

hasType : (fc : FileContext)
       -> (ty : Ty)
      -> {types : List Ty}
       -> (r  : Result types)
             -> Build (Term types ty)
hasType fc ty res with (view (decEq ty) res)
  hasType fc type (R ctxt type term) | (V (Yes Refl))
    = Right term

  hasType fc ty (R ctxt type term) | (V (No contra))
    = Left (Err fc (MMatch ty type))

data Func : List Ty -> Type where
  F : (a,b : Ty) -> Term ctxt (TyFunc a b) -> Func ctxt

isFunc : (fc : FileContext)
     -> {types : List Ty}
      -> (r  : Result types)
            -> Build (Func types)
isFunc fc r with (view isFunc r)
  isFunc fc (R ctxt (TyFunc a b) term) | (V M)
    = Right (F a b term)
  isFunc fc (R ctxt type term) | (V F)
    = Left (Err fc ExpFunc)

data PairRes : List Ty -> Type where
  T : (a,b : Ty) -> Term ctxt (TyProduct a b) -> PairRes ctxt

isPair : (fc : FileContext)
      -> {types : List Ty}
      -> (r  : Result types)
            -> Build (PairRes types)
isPair fc r with (view isProduct r)
  isPair fc (R ctxt (TyProduct a b) term) | (V M)
    = Right (T a b term)
  isPair fc (R ctxt type term) | (V F)
    = Left (Err fc (ExpProduct))

data SumRes : List Ty -> Type where
  V : (a,b : Ty) -> Term ctxt (TySum a b) -> SumRes ctxt

isSum : (fc : FileContext)
     -> {types : List Ty}
     -> (r  : Result types)
           -> Build (SumRes types)
isSum fc r with (view isSum r)
  isSum fc (R ctxt (TySum a b) term) | (V M)
    = Right (V a b term)
  isSum fc (R ctxt type term) | (V F)
    = Left (Err fc (ExpSum))

isList : (fc : FileContext)
      -> {types : List Ty}
      -> (r  : Result types)
            -> Build (ty ** Term types (TyList ty))
isList fc r with (view isList r)
  isList fc (R ctxt (TyList a) term) | (V M)
    = Right (a ** term)

  isList fc (R ctxt type term) | (V F)
    = Left (Err fc ExpList)

Context : List Ty -> Type
Context = Context Ty

build : {types : List Ty}
     -> (ctxt  : Context types)
     -> (expr  : Expr)
              -> Build (Result types)
build ctxt (Ref fc x) with (isBound x ctxt)
  build ctxt (Ref fc x) | (Yes prf) with (mkNameless prf)
    build ctxt (Ref fc x) | (Yes prf) | (N (I name type) y idx)
      = pure (R ctxt type (Var idx))

  build ctxt (Ref fc x) | (No _ contra)
    = Left (Err fc (NotName x))

build ctxt (S fc y)
  = pure (R ctxt TyString (B y))
build ctxt (B fc y)
  = pure (R ctxt TyBool (B y))

build ctxt (C fc y)
  = pure (R ctxt TyChar (B y))

build ctxt (N fc k)
  = pure (R ctxt TyNat (B k))

build ctxt (UOp fc k expr)
  = do res <- build ctxt expr

       case k of
         BNot => do b <- isBuiltin fc Bool res
                    pure (R ctxt TyBool (UOp BNot b))

         (SOp SIZE) => do s <- isBuiltin fc Str res
                          pure (R ctxt TyNat (UOp (SOp SIZE) s))

         (SOp PACK) => do ss <- isListOf fc TyChar res
                          pure (R ctxt TyString (UOp (SOp PACK) ss))


         (SOp UNPACK) => do ss <- isBuiltin fc Str res
                            pure (R ctxt (TyList TyChar) (UOp (SOp UNPACK) ss))

         (COp TOSTR) => do s <- isBuiltin fc Chr res
                           pure (R ctxt TyString (UOp (COp TOSTR) s))

         (COp ORD) => do s <- isBuiltin fc Chr res
                         pure (R ctxt TyNat (UOp (COp ORD) s))

         (COp CHAR) => do s <- isBuiltin fc Nat res
                          pure (R ctxt TyChar (UOp (COp CHAR) s))


build ctxt (BOp fc k l r)
  = do lres <- build ctxt l
       rres <- build ctxt r
       case k of
         (NOp x) => do l' <- isBuiltin fc Nat lres
                       r' <- isBuiltin fc Nat rres
                       pure (R ctxt TyNat (BOp (NOp x) l' r'))

         (BOp x) => do l' <- isBuiltin fc Bool lres
                       r' <- isBuiltin fc Bool rres
                       pure (R ctxt TyBool (BOp (BOp x) l' r'))

         NCmp => do l' <- isBuiltin fc Nat lres
                    r' <- isBuiltin fc Nat rres
                    pure (R ctxt TyBool (BOp NCmp l' r'))

build ctxt (MatchPair fc p a b body)
  = do pres <- build ctxt p
       T tyA tyB tup <- isPair fc pres
       R _ tyR b <- build (I b tyB :: I a tyA :: ctxt) body
       pure (R ctxt tyR (MatchPair tup b))

build ctxt (MatchList fc c e h t body)
  = do cres <- build ctxt c
       l <- isList fc cres
       R _ tyE emps <- build ctxt e

       R _ tyB cons <- build (I t (TyList (fst l)) :: I h (fst l) :: ctxt) body

       case decEq tyE tyB of
         No contra => Left (Err fc (MMatch tyE tyB))
         Yes Refl => pure (R ctxt tyE (MatchList (snd l) emps cons))

build ctxt (MatchSum  fc c l bl r br)
  = do cres <- build ctxt c
       V a b v <- isSum fc cres

       R _ tyL this <- build (I l a :: ctxt) bl
       R _ tyR that <- build (I r b :: ctxt) br

       case decEq tyL tyR of
         No contra => Left (Err fc (MMatch tyL tyR))
         Yes Refl => pure (R ctxt tyL (MatchSum v this that))

build ctxt (Empty fc ty)
  = pure (R ctxt (TyList ty) Empty)

build ctxt (Extend fc head tail)
  = do R _ ty h <- build ctxt head
       tres <- build ctxt tail
       t <- isListOf fc ty tres
       pure (R ctxt (TyList ty) (Extend h t))

build ctxt (Pair fc x y)
  = do (R _ tyA a) <- build ctxt x
       (R _ tyB b) <- build ctxt y

       pure (R ctxt (TyProduct tyA tyB) (Pair a b))

build ctxt (This fc t (TySum x y))
 = do tres <- build ctxt t
      t <- hasType fc x tres
      pure (R ctxt (TySum x y) (This t))

build ctxt (This fc t _) = Left (Err fc ExpSum)

build ctxt (That fc t (TySum x y))
 = do tres <- build ctxt t
      t <- hasType fc y tres
      pure (R ctxt (TySum x y) (That t))

build ctxt (That fc t _) = Left (Err fc ExpSum)

build ctxt (Cond fc c tt ff)
  = do cres <- build ctxt c
       b <- isBuiltin fc Bool cres

       R _ tyT t <- build ctxt tt

       fres <- build ctxt ff
       f <- hasType fc tyT fres

       pure (R ctxt tyT (Cond b t f))

build ctxt (Let fc x ty rec value body)
  = if rec
    then do R _ tyE e <- build (I x ty :: ctxt) value
            case decEq ty tyE of
                 No contra => Left (Err fc (MMatch ty tyE))
                 Yes Refl =>
                   do R _ tyB b <- build (I x tyE :: ctxt) body
                      pure (R ctxt tyB (Let (Rec e) b))

    else do R _ tyE e <- build                 ctxt  value
            case decEq ty tyE of
              No _ => Left (Err fc (MMatch ty tyE))
              Yes Refl =>
                do R _ tyB b <- build (I x tyE :: ctxt) body
                   pure (R ctxt tyB (Let e b))

build ctxt (Fun fc x ty body)
  = do R _ tyB b <- build (I x ty :: ctxt) body
       pure (R ctxt (TyFunc ty tyB) (Fun ty b))

build ctxt (App fc f a)
  = do fres <- build ctxt f
       F exp ret f' <- isFunc fc fres

       R _ given a' <- build ctxt a

       case decEq exp given of
         Yes Refl => pure (R ctxt ret (App f' a'))
         No contra => Left (Err fc (MMatch (TyFunc exp ret) given))

build ctxt (TheUnit fc)
  = pure (R ctxt TyUnit U)

build ctxt (The fc ty expr)
  = do eres <- build ctxt expr
       e <- hasType fc ty eres
       pure (R ctxt ty e)

namespace Closed

  export
  build : (e : Expr)
            -> IO (Build (DPair Ty (Term Nil)))
  build e
    = case build Nil e of
       Left err => pure (Left err)
       Right (R [] type inst) => pure (Right (type ** inst))

-- [ EOF ]
