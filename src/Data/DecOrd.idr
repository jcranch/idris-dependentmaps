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

{-
EqIsDec Nat where
  eqDecides 0 0 = DecidesT Refl
  eqDecides (S m) 0 = DecidesF absurd
  eqDecides 0 (S n) = DecidesF absurd
  eqDecides (S m) (S n) = ?what
-}


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

{-
OrdCompatible Nat where
  eqOrdCompat 0 0 = EQEq
  eqOrdCompat (S m) 0 = GTNotEq
  eqOrdCompat 0 (S n) = LTNotEq
  eqOrdCompat (S m) (S n) = case eqOrdCompat m n of
    EQEq => EQEq
    GTNotEq => GTNotEq
    LTNotEq => LTNotEq
-}


data OrdDecides : (a -> a -> Type) -> (x : a) -> (y : a) -> Ordering -> Type where
  DecidesLT : {0 r : a -> a -> Type} -> r x y -> ((x = y) -> Void) -> (r y x -> Void) -> OrdDecides r x y LT
  DecidesEQ : {0 r : a -> a -> Type} -> (r x y -> Void) -> (x = y) -> (r y x -> Void) -> OrdDecides r x y EQ
  DecidesGT : {0 r : a -> a -> Type} -> (r x y -> Void) -> ((x = y) -> Void) -> r y x -> OrdDecides r x y GT

interface Ord a => DecOrd a (r : a -> a -> Type) | a where
  decOrd : (x : a) -> (y : a) -> OrdDecides r x y (compare x y)

{-
DecOrd Nat LT where
  decOrd 0 0 = DecidesEQ absurd Refl absurd
  decOrd 0 (S n) = DecidesLT (LTESucc LTEZero) absurd absurd
  decOrd (S m) 0 = DecidesGT absurd absurd (LTESucc LTEZero)
  decOrd (S m) (S n) = case compare m n of 
    EQ => case decOrd m n of
      DecidesEQ p q r => DecidesEQ ?a ?b ?c
    LT => case decOrd m n of
      DecidesLT p q r => DecidesLT ?d ?e ?f
    GT => case decOrd m n of
      DecidesGT p q r => DecidesGT ?g ?h ?i
-}

{-
decOrdEq : DecOrd a r => DecEq x where
  decEq x y = case decOrd x y of
    DecidesLT _ p _ => No p
-}
