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

import Toolkit.Data.Location

import Toolkit.Data.DList
import Toolkit.Data.DList.Elem

import Olaf

import Olaf.AST

%default total

namespace Context
  public export
  data Name : Ty -> Type where
    MkName : String -> (ty : Ty) -> Name ty

  public export
  Context : List Ty -> Type
  Context = DList Ty Name

  data HasName : (str : String) -> (name : Name type) -> Type where
    Y : HasName str (MkName str type)

  nameNotSame : (str = x -> Void) -> HasName str (MkName x type) -> Void
  nameNotSame f Y = f Refl

  hasName : (str : String)
         -> (name : Name type)
                 -> Dec (HasName str name)
  hasName str (MkName x type) with (decEq str x)
    hasName x (MkName x type) | (Yes Refl)
      = Yes Y
    hasName str (MkName x type) | (No contra)
      = No (nameNotSame contra)

  notInRest : (HasName str e -> Void) -> (DPair Ty (\t => Elem Ty Name (MkName str t) rest) -> Void) -> DPair Ty (\t => Elem Ty Name (MkName str t) (e :: rest)) -> Void
  notInRest f g (MkDPair type (H (Same Refl Refl)))
    = f (Y)
  notInRest f g (MkDPair fst (T later))
    = g (MkDPair fst later)

  isEmpty : DPair Ty (\t => Elem Ty Name (MkName str t) []) -> Void
  isEmpty (MkDPair _ (H x)) impossible

  export
  isName : (str  : String)
        -> (ctxt : Context types)
                -> Dec (t : Ty ** Elem Ty Name (MkName str t) ctxt)
  isName str [] = No isEmpty
  isName str (elem :: rest) with (hasName str elem)
    isName str ((MkName str x) :: rest) | (Yes Y)
      = Yes (MkDPair x (H (Same Refl Refl)))
    isName str (elem :: rest) | (No contra) with (isName str rest)
      isName str (elem :: rest) | (No contra) | (Yes (MkDPair x prf))
        = Yes (MkDPair x (T prf))
      isName str (elem :: rest) | (No contra) | (No f)
        = No (notInRest contra f)


  export
  mkVar : {ctxt  : Context types}
       -> (prf   : Elem Ty Name (MkName str t) ctxt)
                -> Elem t types
  mkVar (H (Same Refl Refl)) = Here
  mkVar (T later) = There (mkVar later)

namespace Result

  public export
  data Result : (types : List Ty)
                      -> Type
    where
      R : (ctxt : Context types)
       -> (type : Ty)
       -> (term : Term types type)
               -> Result types

  public export
  data View : (p   : Ty -> Type)
           -> (res : Result types)
                   -> Type where

    V : {ctxt : Context types}
     -> {term : Term types type}
     -> (prf  : p type)
             -> View p (R ctxt type term)

  export
  view : (f   : (type : Ty) -> p type)
      -> (res : Result types)
             -> View p res
  view f (R ctxt type term) with (f type)
    view f (R ctxt type term) | prf = V prf

public export
data Error : Type where
  Err : FileContext -> Error -> Error
  ExpSum : Error
  ExpFunc : Error
  ExpProduct : Error
  ExpList : Error
  NotName : String -> Error
  MMatch : (x,y : Ty) -> Error

public export
Build : Type -> Type
Build = Either Error

namespace Type
  export
  isBuiltin : (fc : FileContext)
           -> (b  : Builtin)
           -> (r  : Result types)
                 -> Build (Term types (TyBuiltin b))
  isBuiltin fc b r with (view (isBuiltin b) r)
    isBuiltin fc b (R ctxt (TyBuiltin b) term) | (V M)
      = Right term
    isBuiltin fc b (R ctxt type term) | (V F)
      = Left (Err fc (MMatch (TyBuiltin b) type))


  export
  isListOf : (fc : FileContext)
          -> (ty : Ty)
          -> (r  : Result types)
                -> Build (Term types (TyList ty))
  isListOf fc ty r with (view (isListOf ty) r)
    isListOf fc ty (R ctxt (TyList ty) term) | (V M)
      = Right term
    isListOf fc ty (R ctxt type term) | (V F)
      = Left (Err fc (MMatch (TyList ty) type))

  export
  hasType : (fc : FileContext)
         -> (ty : Ty)
         -> (r  : Result types)
               -> Build (Term types ty)
  hasType fc ty res with (view (decEq ty) res)
    hasType fc type (R ctxt type term) | (V (Yes Refl))
      = Right term

    hasType fc ty (R ctxt type term) | (V (No contra))
      = Left (Err fc (MMatch ty type))

  public export
  data Func : List Ty -> Type where
    F : (a,b : Ty) -> Term ctxt (TyFunc a b) -> Func ctxt

  export
  isFunc : (fc : FileContext)
        -> (r  : Result types)
              -> Build (Func types)
  isFunc fc r with (view isFunc r)
    isFunc fc (R ctxt (TyFunc a b) term) | (V M)
      = Right (F a b term)
    isFunc fc (R ctxt type term) | (V F)
      = Left (Err fc ExpFunc)

  public export
  data PairRes : List Ty -> Type where
    T : (a,b : Ty) -> Term ctxt (TyProduct a b) -> PairRes ctxt

  public export
  isPair : (fc : FileContext)
        -> (r  : Result types)
              -> Build (PairRes types)
  isPair fc r with (view isProduct r)
    isPair fc (R ctxt (TyProduct a b) term) | (V M)
      = Right (T a b term)
    isPair fc (R ctxt type term) | (V F)
      = Left (Err fc (ExpProduct))

  public export
  data SumRes : List Ty -> Type where
    V : (a,b : Ty) -> Term ctxt (TySum a b) -> SumRes ctxt

  public export
  isSum : (fc : FileContext)
       -> (r  : Result types)
             -> Build (SumRes types)
  isSum fc r with (view isSum r)
    isSum fc (R ctxt (TySum a b) term) | (V M)
      = Right (V a b term)
    isSum fc (R ctxt type term) | (V F)
      = Left (Err fc (ExpSum))


  public export
  isList : (fc : FileContext)
        -> (r  : Result types)
              -> Build (ty ** Term types (TyList ty))
  isList fc r with (view isList r)
    isList fc (R ctxt (TyList a) term) | (V M)
      = Right (a ** term)

    isList fc (R ctxt type term) | (V F)
      = Left (Err fc ExpList)

namespace Expr
  export
  build : Context types
       -> Expr
       -> Build (Result types)
  build ctxt (Ref fc y) with (isName y ctxt)
    build ctxt (Ref fc y) | (Yes (ty ** prf)) = pure (R ctxt ty (Var (mkVar prf)))
    build ctxt (Ref fc y) | (No contra)
      = Left (Err fc (NotName y))

  build ctxt (S fc y) = pure (R ctxt TyString (B y))
  build ctxt (B fc y) = pure (R ctxt TyBool   (B y))
  build ctxt (C fc y) = pure (R ctxt TyChar   (B y))
  build ctxt (N fc k) = pure (R ctxt TyNat    (B k))

  build ctxt (UOp fc k expr)
    = do res <- build ctxt expr

         case k of
           BNot => do b <- Type.isBuiltin fc Bool res
                      pure (R ctxt TyBool (UOp BNot b))

           (SOp SIZE) => do s <- Type.isBuiltin fc Str res
                            pure (R ctxt TyNat (UOp (SOp SIZE) s))

           (SOp PACK) => do ss <- isListOf fc TyChar res
                            pure (R ctxt TyString (UOp (SOp PACK) ss))


           (SOp UNPACK) => do ss <- Type.isBuiltin fc Str res
                              pure (R ctxt (TyList TyChar) (UOp (SOp UNPACK) ss))

           (COp TOSTR) => do s <- Type.isBuiltin fc Chr res
                             pure (R ctxt TyString (UOp (COp TOSTR) s))

           (COp ORD) => do s <- Type.isBuiltin fc Chr res
                           pure (R ctxt TyNat (UOp (COp ORD) s))

           (COp CHAR) => do s <- Type.isBuiltin fc Nat res
                            pure (R ctxt TyChar (UOp (COp CHAR) s))


  build ctxt (BOp fc k l r)
    = do lres <- build ctxt l
         rres <- build ctxt r
         case k of
           (NOp x) => do l' <- Type.isBuiltin fc Nat lres
                         r' <- Type.isBuiltin fc Nat rres
                         pure (R ctxt TyNat (BOp (NOp x) l' r'))

           (BOp x) => do l' <- Type.isBuiltin fc Bool lres
                         r' <- Type.isBuiltin fc Bool rres
                         pure (R ctxt TyBool (BOp (BOp x) l' r'))

           NCmp => do l' <- Type.isBuiltin fc Nat lres
                      r' <- Type.isBuiltin fc Nat rres
                      pure (R ctxt TyBool (BOp NCmp l' r'))

  build ctxt (MatchPair fc p a b body)
    = do pres <- build ctxt p
         T tyA tyB tup <- isPair fc pres
         R _ tyR b <- build (MkName b tyB :: MkName a tyA :: ctxt) body
         pure (R ctxt tyR (MatchPair tup b))

  build ctxt (MatchList fc c e h t body)
    = do cres <- build ctxt c
         l <- isList fc cres
         R _ tyE emps <- build ctxt e

         R _ tyB cons <- build (MkName t (TyList (fst l)) :: MkName h (fst l) :: ctxt) body

         case decEq tyE tyB of
           No contra => Left (Err fc (MMatch tyE tyB))
           Yes Refl => pure (R ctxt tyE (MatchList (snd l) emps cons))

  build ctxt (MatchSum  fc c l bl r br)
    = do cres <- build ctxt c
         V a b v <- isSum fc cres

         R _ tyL this <- build (MkName l a :: ctxt) bl
         R _ tyR that <- build (MkName r b :: ctxt) br

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
      then do R _ tyE e <- build (MkName x ty :: ctxt) value
              case decEq ty tyE of
                   No contra => Left (Err fc (MMatch ty tyE))
                   Yes Refl =>
                     do R _ tyB b <- build (MkName x tyE :: ctxt) body
                        pure (R ctxt tyB (Let (Rec e) b))

      else do R _ tyE e <- build                 ctxt  value
              case decEq ty tyE of
                No _ => Left (Err fc (MMatch ty tyE))
                Yes Refl =>
                  do R _ tyB b <- build (MkName x tyE :: ctxt) body
                     pure (R ctxt tyB (Let e b))

  build ctxt (Fun fc x ty body)
    = do R _ tyB b <- build (MkName x ty :: ctxt) body
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
            -> IO (Build (Result Nil))
  build e
    = case build Nil e of
       Left err => pure (Left err)
       Right res => pure (Right res)

-- [ EOF ]
