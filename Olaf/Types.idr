module Olaf.Types

import Decidable.Equality

import Data.Nat
import Data.String
import Data.List
import Data.List.Elem
import Data.Bool.Xor

%default total

public export
data Builtin = Nat | Bool | Str | Chr

namespace Builtin

  natNotBool : Types.Nat = Types.Bool -> Void
  natNotBool Refl impossible

  natNotStr : Types.Nat = Types.Str -> Void
  natNotStr Refl impossible

  natNotChr : Types.Nat = Types.Chr -> Void
  natNotChr Refl impossible

  boolNotStr : Types.Bool = Types.Str -> Void
  boolNotStr Refl impossible

  boolNotChr : Types.Bool = Types.Chr -> Void
  boolNotChr Refl impossible

  strNotChr : Types.Str = Chr -> Void
  strNotChr Refl impossible

  export
  DecEq Builtin where
    decEq Nat Nat = Yes Refl
    decEq Nat Bool = No natNotBool
    decEq Nat Str = No natNotStr
    decEq Nat Chr = No natNotChr

    decEq Bool Nat = No (negEqSym natNotBool)
    decEq Bool Bool = Yes Refl
    decEq Bool Str = No boolNotStr
    decEq Bool Chr = No boolNotChr

    decEq Str Nat = No (negEqSym natNotStr)
    decEq Str Bool = No (negEqSym boolNotStr)
    decEq Str Str = Yes Refl
    decEq Str Chr = No strNotChr

    decEq Chr Nat = No (negEqSym natNotChr)
    decEq Chr Bool = No (negEqSym boolNotChr)
    decEq Chr Str = No (negEqSym strNotChr)
    decEq Chr Chr = Yes Refl

namespace Ty
  public export
  data Ty = TyBuiltin Builtin
          | TyList Ty | TyProduct Ty Ty | TySum Ty Ty
          | TyFunc Ty Ty
          | TyUnit

public export
TyNat, TyBool, TyString, TyChar : Ty
TyNat  = TyBuiltin Nat
TyBool = TyBuiltin Bool
TyString = TyBuiltin Str
TyChar   = TyBuiltin Chr

public export
PrimTy : Builtin -> Type
PrimTy Nat = Nat
PrimTy Bool = Bool
PrimTy Str = String
PrimTy Chr = Char

builtInsNotSame : (x = z -> Void) -> TyBuiltin x = TyBuiltin z -> Void
builtInsNotSame f Refl = f Refl

bNotL : TyBuiltin x = TyList z -> Void
bNotL Refl impossible

bNotP : TyBuiltin x = TyProduct z w -> Void
bNotP Refl impossible

bNotS : TyBuiltin x = TySum z w -> Void
bNotS Refl impossible

bNotF : TyBuiltin x = TyFunc z w -> Void
bNotF Refl impossible

bNotU : TyBuiltin x = TyUnit -> Void
bNotU Refl impossible

listType : (x = z -> Void) -> TyList x = TyList z -> Void
listType contra Refl = contra Refl

lNotP : TyList x = TyProduct z w -> Void
lNotP Refl impossible

lNotS : TyList x = TySum z w -> Void
lNotS Refl impossible

lNotF : TyList x = TyFunc z w -> Void
lNotF Refl impossible

lNotU : TyList x = TyUnit -> Void
lNotU Refl impossible

pNotU : TyProduct x z = TyUnit -> Void
pNotU Refl impossible

pNotS : TyProduct x z = TySum w v -> Void
pNotS Refl impossible

pNotF : TyProduct x z = TyFunc w v -> Void
pNotF Refl impossible

productF : (x = w -> Void) -> TyProduct x z = TyProduct w v -> Void
productF f Refl = f Refl

productS : (z = v -> Void) -> TyProduct w z = TyProduct w v -> Void
productS f Refl = f Refl

sumS : (z = v -> Void) -> TySum w z = TySum w v -> Void
sumS f Refl = f Refl

sumF : (x = w -> Void) -> TySum x z = TySum w v -> Void
sumF f Refl = f Refl

sNotF : TySum x z = TyFunc w v -> Void
sNotF Refl impossible

sNotU : TySum x z = TyUnit -> Void
sNotU Refl impossible

fNotU : TyFunc x z = TyUnit -> Void
fNotU Refl impossible

funcP : (x = w -> Void) -> TyFunc x z = TyFunc w v -> Void
funcP f Refl = f Refl

funcR : (z = v -> Void) -> TyFunc w z = TyFunc w v -> Void
funcR f Refl = f Refl

decEq : (x,y : Ty) -> Dec (x === y)
decEq (TyBuiltin x) y with (y)
  decEq (TyBuiltin x) y | (TyBuiltin z) with (decEq x z)
    decEq (TyBuiltin z) y | (TyBuiltin z) | (Yes Refl) = Yes Refl
    decEq (TyBuiltin x) y | (TyBuiltin z) | (No contra)
      = No (builtInsNotSame contra)

  decEq (TyBuiltin x) y | (TyList z)      = No bNotL
  decEq (TyBuiltin x) y | (TyProduct z w) = No bNotP
  decEq (TyBuiltin x) y | (TySum z w)     = No bNotS
  decEq (TyBuiltin x) y | (TyFunc z w)    = No bNotF
  decEq (TyBuiltin x) y | TyUnit          = No bNotU

decEq (TyList x) y with (y)
  decEq (TyList x) y | (TyBuiltin z) = No (negEqSym bNotL)
  decEq (TyList x) y | (TyList z) with (decEq x z)
    decEq (TyList z) y | (TyList z) | (Yes Refl) = Yes Refl
    decEq (TyList x) y | (TyList z) | (No contra)
      = No (listType contra)

  decEq (TyList x) y | (TyProduct z w) = No lNotP
  decEq (TyList x) y | (TySum z w)     = No lNotS
  decEq (TyList x) y | (TyFunc z w)    = No lNotF
  decEq (TyList x) y | TyUnit          = No lNotU

decEq (TyProduct x z) y with (y)
  decEq (TyProduct x z) y | (TyBuiltin w)
    = No (negEqSym bNotP)
  decEq (TyProduct x z) y | (TyList w)
    = No (negEqSym lNotP)

  decEq (TyProduct x z) y | (TyProduct w v) with (decEq x w)
    decEq (TyProduct w z) y | (TyProduct w v) | (Yes Refl) with (decEq z v)
      decEq (TyProduct w z) y | (TyProduct w z) | (Yes Refl) | (Yes Refl)
        = Yes Refl

      decEq (TyProduct w z) y | (TyProduct w v) | (Yes Refl) | (No contra)
        = No (productS contra)
    decEq (TyProduct x z) y | (TyProduct w v) | (No contra)
      = No (productF contra)

  decEq (TyProduct x z) y | (TySum w v)     = No pNotS
  decEq (TyProduct x z) y | (TyFunc w v)    = No pNotF
  decEq (TyProduct x z) y | TyUnit          = No pNotU

decEq (TySum x z) y with (y)
  decEq (TySum x z) y | (TyBuiltin w) = No (negEqSym bNotS)
  decEq (TySum x z) y | (TyList w) = No (negEqSym lNotS)
  decEq (TySum x z) y | (TyProduct w v) = No (negEqSym pNotS)

  decEq (TySum x z) y | (TySum w v) with (decEq x w)
    decEq (TySum w z) y | (TySum w v) | (Yes Refl) with (decEq z v)
      decEq (TySum w z) y | (TySum w z) | (Yes Refl) | (Yes Refl)
        = Yes Refl
      decEq (TySum w z) y | (TySum w v) | (Yes Refl) | (No contra)
        = No (sumS contra)

    decEq (TySum x z) y | (TySum w v) | (No contra)
       = No (sumF contra)

  decEq (TySum x z) y | (TyFunc w v) = No sNotF
  decEq (TySum x z) y | TyUnit = No sNotU

decEq (TyFunc x z) y with (y)
  decEq (TyFunc x z) y | (TyBuiltin w) = No (negEqSym bNotF)
  decEq (TyFunc x z) y | (TyList w) = No (negEqSym lNotF)
  decEq (TyFunc x z) y | (TyProduct w v) = No (negEqSym pNotF)
  decEq (TyFunc x z) y | (TySum w v) = No (negEqSym sNotF)

  decEq (TyFunc x z) y | (TyFunc w v) with (decEq x w)
    decEq (TyFunc w z) y | (TyFunc w v) | (Yes Refl) with (decEq z v)
      decEq (TyFunc w z) y | (TyFunc w z) | (Yes Refl) | (Yes Refl)
        = Yes Refl
      decEq (TyFunc w z) y | (TyFunc w v) | (Yes Refl) | (No contra)
        = No (funcR contra)
    decEq (TyFunc x z) y | (TyFunc w v) | (No contra)
      = No (funcP contra)

  decEq (TyFunc x z) y | TyUnit = No fNotU

decEq TyUnit y with (y)
  decEq TyUnit y | (TyBuiltin x) = No (negEqSym bNotU)
  decEq TyUnit y | (TyList x) = No (negEqSym lNotU)
  decEq TyUnit y | (TyProduct x z) = No (negEqSym pNotU)
  decEq TyUnit y | (TySum x z) = No (negEqSym sNotU)
  decEq TyUnit y | (TyFunc x z) = No (negEqSym fNotU)
  decEq TyUnit y | TyUnit = Yes Refl

export
DecEq Ty where
  decEq = Types.decEq

namespace View
  namespace IsBuiltin
   public export
   data IsBuiltin : Builtin -> Ty -> Type where
     M : IsBuiltin n (TyBuiltin n)
     F : IsBuiltin n type

   export
   isBuiltin : (b : Builtin) -> (type : Ty) -> IsBuiltin b type
   isBuiltin b (TyBuiltin x) with (decEq b x)
     isBuiltin x (TyBuiltin x) | (Yes Refl) = M
     isBuiltin b (TyBuiltin x) | (No contra) = F
   isBuiltin _ _ = F



  namespace IsFunc
    public export
    data IsFunc : Ty -> Type where
      M : IsFunc (TyFunc a b)
      F : IsFunc type

    export
    isFunc : (type : Ty) -> IsFunc type
    isFunc (TyFunc a b) = M
    isFunc _ = F

  namespace IsSum
    public export
    data IsSum : Ty -> Type where
      M : IsSum (TySum a b)
      F : IsSum type

    export
    isSum : (type : Ty) -> IsSum type
    isSum (TySum a b) = M
    isSum _ = F

  namespace IsProduct
    public export
    data IsProduct : Ty -> Type where
      M : IsProduct (TyProduct a b)
      F : IsProduct type

    export
    isProduct : (type : Ty) -> IsProduct type
    isProduct (TyProduct a b) = M
    isProduct _ = F

  namespace IsList
   public export
   data IsList : Ty -> Type where
     M : IsList (TyList a)
     F : IsList type

   export
   isList : (type : Ty) -> IsList type
   isList (TyList a) = M
   isList _ = F

  namespace IsListOf

    public export
    data IsListOf : (inner, list : Ty) -> Type where
      M : IsListOf a (TyList a)
      F : IsListOf a other

    export
    isListOf : (inner, list : Ty) -> IsListOf inner list
    isListOf inner (TyList a) with (Types.decEq inner a)
      isListOf a (TyList a) | (Yes Refl) = M
      isListOf inner (TyList a) | (No contra) = F
    isListOf _ _ = F

  namespace IsUnit
   public export
   data IsUnit : Ty -> Type where
     M : IsUnit TyUnit
     F : IsUnit type

   export
   isUnit : (type : Ty) -> IsUnit type
   isUnit TyUnit = M
   isUnit _ = F

--  [ EOF ]
