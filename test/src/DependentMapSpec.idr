module Test.DependentMap

import Data.Vect
import Decidable.Equality

import Data.Foldable.Dependent
import Data.Functor.Dependent

import Data.Misc
import Data.DependentMap


l1 : List (DPair Nat (\n => Vect n Nat))
l1 = [(2 ** [1,1]), (3 ** [1,1,1]), (4 ** [1,1,1,1])]

l2 : List (DPair Nat (\n => Vect n Nat))
l2 = [(1 ** [2]), (3 ** [2,2,2]), (5 ** [2,2,2,2,2])]

m1 : DMap Nat (\n => Vect n Nat)
m1 = fromList l1

m2 : DMap Nat (\n => Vect n Nat)
m2 = fromList l2

m3 : DMap Nat (\n => Vect n Nat)
m3 = singleton 4 [3,3,3,3]


-- A simple invariant for testing
trail : DMap Nat (\n => Vect n Nat) -> List (Nat, Nat)
trail = dconcatMap t where
  t : (n : Nat) -> Vect n Nat -> List (Nat, Nat)
  t n v = [(n, sum v)]

trail2 : (Maybe (Vect m Nat), DMap Nat (\n => Vect n Nat)) -> (Maybe (List Nat), List (Nat, Nat))
trail2 (p, q) = (map toList p, trail q)


export
tests : List (Lazy Bool)
tests = [

  length l1 == 3,
  length l2 == 3,

  trail m1 == [(2,2),(3,3),(4,4)],
  trail m2 == [(1,2),(3,6),(5,10)],
  trail m3 == [(4,12)],
  trail (fromList (toList m1)) == [(2,2),(3,3),(4,4)],
  trail (dmap (\i, l => map (+ i) l) m1) == [(2,6),(3,12),(4,20)],

  lookup 1 m1 == Nothing,
  lookup 2 m1 == Just [1,1],
  lookup 3 m1 == Just [1,1,1],
  lookup 4 m1 == Just [1,1,1,1],
  lookup 5 m1 == Nothing,

  trail2 (replace 1 [0] m1) == (Nothing, [(1,0),(2,2),(3,3),(4,4)]),
  trail2 (replace 2 [0,0] m1) == (Just [1,1], [(2,0),(3,3),(4,4)]),
  trail2 (replace 3 [0,0,0] m1) == (Just [1,1,1], [(2,2),(3,0),(4,4)]),
  trail2 (replace 4 [0,0,0,0] m1) == (Just [1,1,1,1], [(2,2),(3,3),(4,0)]),
  trail2 (replace 5 [0,0,0,0,0] m1) == (Nothing, [(2,2),(3,3),(4,4),(5,0)]),

  map trail (extract 2 m1) == (Just [1,1], [(3,3), (4,4)]),
  map trail (extract 5 m1) == (Nothing, [(2,2),(3,3),(4,4)]),
  trail neutral == [],
  trail (m1 <+> m2) == [(1,2),(2,2),(3,6),(4,4),(5,10)],

  toList (KeyView m1) == [2,3,4]]

export
testDependentMap : IO ()
testDependentMap = do
  putStrLn "DependentMap:"
  putStrLn $ if and tests then "  All tests passed!" else "  Some failures."
