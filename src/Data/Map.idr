module Data.Map

import Control.Monad.Identity
import Decidable.Equality

import Data.Filterable
import Data.Filterable.Dependent
import Data.Filterable.Indexed
import Data.Foldable.Dependent
import Data.Foldable.Indexed
import Data.Functor.Dependent
import Data.Functor.Indexed
import Data.Traversable.Dependent
import Data.Traversable.Indexed
import Data.Witherable
import Data.Witherable.Dependent
import Data.Witherable.Indexed
import Data.Withering
import Data.Withering.Dependent

import Data.DependentMap
import Data.Misc


public export
record Map (k : Type) (v : Type) where
  constructor Indep
  dep : DMap k (const v)

export
length : Map k v -> Nat
length = length . dep

export
empty : Map k v
empty = Indep empty

export
null : Map k v -> Bool
null = null . dep

export
{0 k : Type} -> Functor (Map k) where
  map f = Indep . dmap (const f) . dep

export
{0 k : Type} -> IndFunctor k (Map k) where
  imap f = Indep . dmap f . dep

export
{0 k : Type} -> Foldable (Map k) where
  foldl f z = dfoldl (\m, _, x => f m x) z . dep
  foldr f z = dfoldr (\_, x, m => f x m) z . dep
  -- concatMap f = dconcatMap (\_, x => f x) . dep

export
{0 k : Type} -> IndFoldable k (Map k) where
  ifoldl f z = dfoldl f z . dep
  ifoldr f z = dfoldr f z . dep
  iconcatMap f = dconcatMap f . dep

export
{0 k : Type} -> Traversable (Map k) where
  traverse f m = Indep <$> dtraverse (\_, x => f x) (dep m)

export
{0 k : Type} -> IndTraversable k (Map k) where
  itraverse f m = Indep <$> dtraverse f (dep m)

export
{0 k : Type} -> Ord k => Filterable (Map k) where
  mapMaybe f = Indep . dmapMaybe (\_, x => f x) . dep

export
{0 k : Type} -> Ord k => IndFilterable k (Map k) where
  imapMaybe f = Indep . dmapMaybe f . dep

export
{0 k : Type} -> Ord k => Witherable (Map k) where

export
{0 k : Type} -> Ord k => IndWitherable k (Map k) where

export
(Ord k, Eq v) => Eq (Map k v) where
  Indep m == Indep n = indepToList m == indepToList n

export
(Ord k, Ord v) => Ord (Map k v) where
  compare (Indep m) (Indep n) = compare (indepToList m) (indepToList n)

-- This takes us into complicated territory; we might *need* the Yes
-- branch since it could have computational content. But I'm not quite
-- sure how to build it.
export
(DecEq k, DecEq v) => DecEq (Map k v) where
  decEq (Indep m) (Indep n) = case decEq (indepToList m) (indepToList n) of
    Yes _ => Yes ?shouldExplainWhy
    No _ => No ?shouldExplainWhyNot


||| Union of maps
|||
||| Prefers the values in the second argument
export
union : Ord k => Map k v -> Map k v -> Map k v
union m n = Indep (union (dep m) (dep n))

export
Ord k => Semigroup (Map k v) where
  (<+>) = union

export
Ord k => Monoid (Map k v) where
  neutral = empty

export
lookup : Ord k => k -> Map k v -> Maybe v
lookup x m = map dsnd . basicLookup x $ dep m

export
singleton : k -> v -> Map k v
singleton k = Indep . singleton k

export
replace : Ord k => k -> v -> Map k v -> (Maybe v, Map k v)
replace x a m = let
  (f, n) = basicReplace x a $ dep m
  in (map dsnd f, Indep n)

export
insert : Ord k => k -> v -> Map k v -> Map k v
insert x a = Indep . snd . basicReplace x a . dep

export
alter : (Ord k) => k -> (Maybe v -> Maybe v) -> Map k v -> Map k v
alter x g = Indep . basicAlter x (map (MkDPair x) . g . map dsnd) . dep


export
alterF : (Functor f, Ord k) => (x : k) -> (Maybe v -> f (Maybe v)) -> Map k v -> f (Map k v)
alterF x g = map Indep . basicAlterF x (map (map (MkDPair x)) . g . map dsnd) . dep

export
splitAt : Ord k => k -> Map k v -> (Map k v, Maybe v, Map k v)
splitAt x m = let
  (l, f, r) = basicSplitAt x $ dep m
  in (Indep l, map dsnd f, Indep r)

export
concatenate : Ord k => Map k v -> Map k v -> Map k v
concatenate m n = Indep (concatenate (dep m) (dep n))

export
delete : Ord k => k -> Map k v -> Map k v
delete x = Indep . delete x . dep

export
extract : (Ord k) => k -> Map k v -> (Maybe v, Map k v)
extract x m = let
  (f, n) = basicExtract x $ dep m
  in (map dsnd f, Indep n)

export
fromList : (Ord k, Foldable t, Functor t) => t (k, v) -> Map k v
fromList = Indep . fromList . map f where
  f : Pair k v -> DPair k (const v)
  f (MkPair a x) = MkDPair a x

export
mconcatMap : Monoid m => (k -> v -> m) -> Map k v -> m
mconcatMap f = dconcatMap f . dep

export
minView : Map k v -> Maybe ((k, v), Map k v)
minView m = case minView $ dep m of
  Just (MkDPair x a, n) => Just ((x, a), Indep n)
  Nothing => Nothing

export
maxView : Map k v -> Maybe (Map k v, (k, v))
maxView m = case maxView $ dep m of
  Just (n, MkDPair x a) => Just (Indep n, (x, a))
  Nothing => Nothing

export
singletonView : Map k v -> Maybe (k, v)
singletonView m = case singletonView $ dep m of
  Just (MkDPair x a) => Just (x, a)
  Nothing => Nothing

export
mergeA : (Applicative f, Ord k)
      => Withering f k a c
      -> Withering f k b c
      -> (a -> b -> f (Maybe c))
      -> Map k a
      -> Map k b
      -> f (Map k c)
mergeA onL onR onB (Indep m1) (Indep m2) = Indep <$> mergeA (depWithering onL) (depWithering onR) (\_, _ => onB) m1 m2

export
merge : (Ord k)
      => Withering Identity k a c
      -> Withering Identity k b c
      -> (a -> b -> Maybe c)
      -> Map k a
      -> Map k b
      -> Map k c
merge onL onR onB m1 m2 = runIdentity $ mergeA onL onR (\x, y => Id $ onB x y) m1 m2

export
unionWith : (Ord k) => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith f = merge preserving preserving (\x, y => Just $ f x y)

export
intersectionWith : (Ord k) => (a -> b -> c) -> Map k a -> Map k b -> Map k c
intersectionWith f = merge flushing flushing (\x, y => Just $ f x y)

export
intersection : (Ord k) => Map k a -> Map k a -> Map k a
intersection = merge flushing flushing (\x, _ => Just x)

export
difference : (Ord k) => Map k a -> Map k a -> Map k a
difference = merge preserving flushing (\_, _ => Nothing)
