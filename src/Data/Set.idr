module Data.Set

import Control.Applicative.Restricted
import Control.Monad.Restricted
import Data.Foldable.Indexed
import Data.Functor.Dependent
import Data.Functor.Restricted
import Data.DependentMap
import Data.Map


public export
record Set (k : Type) where
  constructor MkSet
  unSet : Map k ()

fromList : Ord k => List k -> Set k
fromList = MkSet . fromList . map (\x => (x,()))

toList : Set k -> List k
toList = ifoldr (\x, _, l => x::l) [] . unSet

RFunctor Ord Set where
  rmap f = fromList . map f . toList

RApplicative Ord Set where
  rpure x = MkSet $ singleton x ()
  rliftA2 f a b = fromList (f <$> toList a <*> toList b)

export
dkeySet : DMap k v -> Set k
dkeySet = MkSet . Indep . dmap (\_, _ => ())

export
keySet : Map k v -> Set k
keySet = dkeySet . dep

export
length : Set k -> Nat
length = length . unSet

export
empty : Set k
empty = MkSet empty

export
null : Set k -> Bool
null = Data.Map.null . unSet

export
isIn : (Ord k) => k -> Set k -> Bool
isIn x (MkSet m) = case lookup x m of
  Nothing => False
  _       => True

export
insert : (Ord k) => k -> Set k -> Set k
insert x (MkSet m) = MkSet $ insert x () m

export
delete : (Ord k) => k -> Set k -> Set k
delete x (MkSet m) = MkSet $ delete x m

export
Foldable Set where
  foldl f z (MkSet m) = ifoldl (\x,k,_ => f x k) z m
  foldr f z (MkSet m) = ifoldr (\k,_,x => f k x) z m

||| The intersection of two sets. In case of differing keys that test
||| equal, it prefers the value in the second set.
export
union : Ord k => Set k -> Set k -> Set k
union (MkSet m1) (MkSet m2) = MkSet $ union m1 m2

||| The intersection of two sets
export
intersection : Ord k => Set k -> Set k -> Set k
intersection (MkSet m1) (MkSet m2) = MkSet $ intersection m1 m2

export
difference : Ord k => Set k -> Set k -> Set k
difference (MkSet m1) (MkSet m2) = MkSet $ difference m1 m2

export
Ord k => Eq (Set k) where
  MkSet a == MkSet b = a == b

export
Ord k => Ord (Set k) where
  compare (MkSet a) (MkSet b) = compare a b


||| A monoid for set unions
public export
record SetUnion (k : Type) where
  constructor MkUnion
  getUnion : Set k

Ord k => Semigroup (SetUnion k) where
  MkUnion a <+> MkUnion b = MkUnion (union a b)

Ord k => Monoid (SetUnion k) where
  neutral = MkUnion empty

||| A semigroup for set intersections (it can't be a monoid, as it has
||| no neutral element).
public export
record SetIntersection (k : Type) where
  constructor MkIntersection
  getIntersection : Set k

Ord k => Semigroup (SetIntersection k) where
  MkIntersection a <+> MkIntersection b = MkIntersection (intersection a b)

RMonad Ord Set where
  rjoin a f = getUnion . foldMap (MkUnion . f) $ Data.Set.toList a

