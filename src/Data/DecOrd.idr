module Data.DecOrd

import Data.Nat
import Decidable.Equality


||| Compatibility between a boolean and a proposition
data Decides : Bool -> Type -> Type where
  DecidesT : p -> Decides True p
  DecidesF : (p -> Void) -> Decides False p


||| Decidable equality compatible with an Eq instance
interface Eq x => EqIsDec x where
  eqDecides : (a : x) -> (b : x) -> Decides (a == b) (a = b)

EqIsDec () where
  eqDecides () () = DecidesT Refl

EqIsDec Bool where
  eqDecides True True = DecidesT Refl
  eqDecides False False = DecidesT Refl
  eqDecides True False = DecidesF absurd
  eqDecides False True = DecidesF absurd


eqPrec : S l = S r -> l = r
eqPrec Refl = Refl

neSucc : (l = r -> Void) -> S l = S r -> Void
neSucc f p = f (eqPrec p)

decSucc : Decides (m == n) (m = n) -> Decides (S m == S n) (S m = S n)
decSucc d with 0 (m == n)
  decSucc (DecidesT r) | True = DecidesT (cong S r)
  decSucc (DecidesF r) | False = DecidesF (neSucc r)

EqIsDec Nat where
  eqDecides 0 0 = DecidesT Refl
  eqDecides (S m) 0 = DecidesF absurd
  eqDecides 0 (S n) = DecidesF absurd
  eqDecides (S m) (S n) = decSucc (eqDecides m n)


data EqOrdCompat : Bool -> Ordering -> Type where
  LTNotEq : EqOrdCompat False LT
  GTNotEq : EqOrdCompat False GT
  EQEq : EqOrdCompat True EQ


||| Types with compatible Eq and Ord instances
interface Ord x => OrdCompatible x where
  eqOrdCompat : (a : x) -> (b : x) -> EqOrdCompat (a == b) (compare a b)

OrdCompatible () where
  eqOrdCompat () () = EQEq

OrdCompatible Bool where
  eqOrdCompat True True = EQEq
  eqOrdCompat False False = EQEq
  eqOrdCompat True False = GTNotEq
  eqOrdCompat False True = LTNotEq

eqOrdCompatSucc : EqOrdCompat (a == b) (compare a b) -> EqOrdCompat (S a == S b) (compare (S a) (S b))
eqOrdCompatSucc {a} {b} c with 0 (a == b) | 0 (compare a b)
  eqOrdCompatSucc EQEq | True | EQ = EQEq
  eqOrdCompatSucc GTNotEq | False | GT = GTNotEq
  eqOrdCompatSucc LTNotEq | False | LT = LTNotEq

OrdCompatible Nat where
  eqOrdCompat 0 0 = EQEq
  eqOrdCompat (S m) 0 = GTNotEq
  eqOrdCompat 0 (S n) = LTNotEq
  eqOrdCompat (S m) (S n) = eqOrdCompatSucc (eqOrdCompat m n)


interface Irreflexive a r | r where
  irrefl : {0 x : a} -> r x x -> Void

||| Alternative version of irreflexivity
irrefl' : Irreflexive a r => {0 x : a} -> {0 y : a} -> r x y -> x = y -> Void
irrefl' p Refl = irrefl p

natIrrefl : LT x x -> Void
natIrrefl (LTESucc y) = natIrrefl y

Irreflexive Nat LT where
  irrefl = natIrrefl

{-
-- Can't get this to work for quantity reasons
totalOrderAntisymmetry : (Irreflexive a r, Transitive a r) => r x y -> r y x -> Void
totalOrderAntisymmetry p q = irrefl (transitive p q)
-}


data Trichotomy : (r : a -> a -> Type) -> a -> a -> Type where
  LT : {0 x : a} -> {0 y : a} -> r x y -> Trichotomy r x y
  EQ : x = y -> Trichotomy r x y
  GT : {0 x : a} -> {0 y : a} -> r y x -> Trichotomy r x y

interface Trichotomous a r | r where
  trichotomy : (x : a) -> (y : a) -> Trichotomy r x y

trichotomySucc : Trichotomy LT m n -> Trichotomy LT (S m) (S n)
trichotomySucc (LT l) = LT (LTESucc l)
trichotomySucc (EQ e) = EQ (cong S e)
trichotomySucc (GT l) = GT (LTESucc l)

Trichotomous Nat LT where
  trichotomy 0 0 = EQ Refl
  trichotomy 0 (S n) = LT (LTESucc LTEZero)
  trichotomy (S m) 0 = GT (LTESucc LTEZero)
  trichotomy (S m) (S n) = trichotomySucc (trichotomy m n)


succLTE : LTE x y -> LTE x (S y)
succLTE LTEZero = LTEZero
succLTE (LTESucc a) = LTESucc (succLTE a)

precLTE : LTE (S x) y -> LTE x y
precLTE (LTESucc z) = succLTE z

Transitive Nat LT where
  transitive a b = transitive a (precLTE b)


||| Very similar to LinearOrder (in Control.TotalOrder) but based off LT rather than LTE
public export
interface (Irreflexive a r, (Transitive a r, Trichotomous a r)) => TotalOrder a r | r where

TotalOrder Nat LT where


data OrdDecides : (a -> a -> Type) -> (x : a) -> (y : a) -> Ordering -> Type where
  DecidesLT : {0 r : a -> a -> Type} -> r x y -> OrdDecides r x y LT
  DecidesEQ : {0 r : a -> a -> Type} -> x = y -> OrdDecides r x y EQ
  DecidesGT : {0 r : a -> a -> Type} -> r y x -> OrdDecides r x y GT

interface (TotalOrder a r, Ord a) => DecOrd a (r : a -> a -> Type) where
  decOrd : (x : a) -> (y : a) -> OrdDecides r x y (compare x y)

data BoolOrder : Bool -> Bool -> Type where
  FalseTrue : BoolOrder False True

Irreflexive Bool BoolOrder where
  irrefl FalseTrue impossible

Trichotomous Bool BoolOrder where
  trichotomy False False = EQ Refl
  trichotomy False True = LT FalseTrue
  trichotomy True False = GT FalseTrue
  trichotomy True True = EQ Refl

Transitive Bool BoolOrder where
  transitive FalseTrue FalseTrue impossible

TotalOrder Bool BoolOrder where

DecOrd Bool BoolOrder where
  decOrd False True = DecidesLT FalseTrue
  decOrd True False = DecidesGT FalseTrue
  decOrd False False = DecidesEQ Refl
  decOrd True True = DecidesEQ Refl

decOrdNatSucc : OrdDecides LT m n (compare m n) -> OrdDecides LT (S m) (S n) (compare (S m) (S n))
decOrdNatSucc {m} {n} c with 0 (compare m n)
  decOrdNatSucc (DecidesLT p) | LT = DecidesLT (LTESucc p)
  decOrdNatSucc (DecidesEQ q) | EQ = DecidesEQ (cong S q)
  decOrdNatSucc (DecidesGT r) | GT = DecidesGT (LTESucc r)

DecOrd Nat LT where
  decOrd 0 0 = DecidesEQ Refl
  decOrd 0 (S n) = DecidesLT (LTESucc LTEZero)
  decOrd (S m) 0 = DecidesGT (LTESucc LTEZero)
  decOrd (S m) (S n) = decOrdNatSucc (decOrd m n)



ordDecidesEq : (Ord a, Irreflexive a r) => {x : a} -> {y : a} -> OrdDecides r x y (compare x y) -> Dec (x = y)
ordDecidesEq d with (compare x y)
  ordDecidesEq (DecidesLT p) | LT = No (irrefl' p)
  ordDecidesEq (DecidesEQ p) | EQ = Yes p
  ordDecidesEq (DecidesGT p) | GT = No (\e => irrefl' p (sym e))
