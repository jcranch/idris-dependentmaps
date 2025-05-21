||| Another implementation
module Data.DependentMap2

import Decidable.Ordering


data Tree : Nat -> (k : Type) -> (v : k -> Type) -> Ord k -> Type where
  Blank : Tree Z k v o
  Branch2 : Tree n k v o -> (x : k) -> v x -> Tree n k v o -> Tree (S n) k v o
  Branch3 : Tree n k v o -> (x : k) -> v x -> Tree n k v o -> (y : k) -> v y -> Tree n k v o -> Tree (S n) k v o

singleton : (x : k) -> (y : v k) -> Tree (S Z) k v o
singleton x y = branch2 Blank x y Blank

{-
appendrTree : (n : Nat) -> Tree n k v o -> (x : k) -> v x -> Either (Tree n k v o) (Tree (S n) k v o)
appendrTree Z Blank x y = singleton x y
appendrTree 
-}

data DMap : (k : Type) -> (v : k -> Type) -> Type where
  M : (o : Ord k) => (n : Nat) -> Tree n k v o -> DMap k v

