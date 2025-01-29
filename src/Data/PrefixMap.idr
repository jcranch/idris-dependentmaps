module Data.PrefixMap

import Data.Map

import Data.Filterable
import Data.Filterable.Indexed
import Data.Foldable.Indexed
import Data.Functor.Indexed
import Data.Traversable.Indexed
import Data.Witherable
import Data.Witherable.Indexed

export
record PrefixMap k v where
  constructor MkPrefix
  content : Maybe v
  children : Map k (PrefixMap k v)

export
empty : PrefixMap k v
empty = MkPrefix Nothing empty

export
null : PrefixMap k v -> Bool
null (MkPrefix Nothing m) = Data.Map.null m
null _ = False

export
nonNull : PrefixMap k v -> Maybe (PrefixMap k v)
nonNull p = if null p then Nothing else Just p

||| Smart constructor, to remove needless children nodes
export
mkPrefix : Ord k => Maybe v -> Map k (PrefixMap k v) -> PrefixMap k v
mkPrefix c = MkPrefix c . mapMaybe nonNull

export
singleton : List k -> v -> PrefixMap k v
singleton [] a = MkPrefix (Just a) empty
singleton (x::xs) a = MkPrefix Nothing . singleton x $ singleton xs a

export
insert : Ord k => List k -> v -> PrefixMap k v -> PrefixMap k v
insert [] a (MkPrefix _ m) = MkPrefix (Just a) m
insert (x::xs) a (MkPrefix c m) = MkPrefix c $ alter x (Just . f) m where
  f : Maybe (PrefixMap k v) -> PrefixMap k v
  f Nothing = singleton xs a
  f (Just n) = insert xs a n

export
commonPrefix : PrefixMap k v -> (List k, PrefixMap k v)
commonPrefix p@(MkPrefix (Just _) _) = ([], p)
commonPrefix p@(MkPrefix Nothing m) = case singletonView m of
  Nothing => ([], p)
  Just (x, q) => let
   (l, r) = commonPrefix q
   in (x::l, r)

export
Functor (PrefixMap k) where
  map f = inner where
    inner : PrefixMap k a -> PrefixMap k b
    inner (MkPrefix c m) = MkPrefix (map f c) (map inner m)

||| For some reason the typechecker gets confused if we just use these
||| definitions of foldl and foldr directly.
our_foldl : (a -> v -> a) -> a -> PrefixMap k v -> a
our_foldl f = inner where
  inner : a -> PrefixMap k v -> a
  inner z (MkPrefix c m) = foldl inner (foldl f z c) m

our_foldr : (v -> a -> a) -> PrefixMap k v -> a -> a
our_foldr f = inner where
  inner : PrefixMap k v -> a -> a
  inner (MkPrefix c m) z = foldr f (foldr inner z m) c

export
Foldable (PrefixMap k) where
  foldl = our_foldl
  foldr f a p = our_foldr f p a

export
Traversable (PrefixMap k) where
  traverse g = inner where
    inner : PrefixMap k a -> f (PrefixMap k b)
    inner (MkPrefix c m) = MkPrefix <$> traverse g c <*> traverse inner m

export
Ord k => Filterable (PrefixMap k) where
  mapMaybe f = inner where
    inner : PrefixMap k a -> PrefixMap k b
    inner (MkPrefix c m) = MkPrefix (mapMaybe f c) (mapMaybe (nonNull . inner) m)

export
Ord k => Witherable (PrefixMap k) where
  wither g = inner where
    inner : PrefixMap k a -> f (PrefixMap k b)
    inner (MkPrefix c m) = MkPrefix <$> wither g c <*> wither (map nonNull . inner) m


||| A specialised indexed map which folds the index as it goes
fmap : (r : a -> k -> a) -> (f : a -> v -> w) -> (z : a) -> PrefixMap k v -> PrefixMap k w
fmap r f = inner where
  inner : a -> PrefixMap k v -> PrefixMap k w
  inner x (MkPrefix c m) = MkPrefix (f x <$> c) (imap (inner . r x) m)

ffoldl : (r : a -> k -> a) -> (f : a -> b -> v -> b) -> (u : b) -> (z : a) -> PrefixMap k v -> b
ffoldl r f = inner where
  inner : b -> a -> PrefixMap k v -> b
  inner u z (MkPrefix c m) = ifoldl (\w => inner w . r z) (foldl (f z) u c) m

ffoldr : (r : a -> k -> a) -> (f : a -> v -> b -> b) -> (z : a) -> PrefixMap k v -> (u : b) -> b
ffoldr r f = inner where
  inner : a -> PrefixMap k v -> b -> b
  inner z (MkPrefix c m) u = foldr (f z) (ifoldr (inner . r z) u m) c

fconcatMap : Monoid s => (r : a -> k -> a) -> (f : a -> v -> s) -> (z : a) -> PrefixMap k v -> s
fconcatMap r f = inner where
  inner : a -> PrefixMap k v -> s
  inner z (MkPrefix c m) = let
    p = iconcatMap (inner . r z) m
    in case c of
      Nothing => p
      Just x => f z x <+> p

ftraverse : Applicative t => (r : a -> k -> a) -> (f : a -> v -> t w) -> (z : a) -> PrefixMap k v -> t (PrefixMap k w)
ftraverse r f = inner where
  inner : a -> PrefixMap k v -> t (PrefixMap k w)
  inner z (MkPrefix c m) = MkPrefix <$> traverse (f z) c <*> itraverse (inner . r z) m

fmapMaybe : Ord k => (r : a -> k -> a) -> (f : a -> v -> Maybe w) -> (z : a) -> PrefixMap k v -> PrefixMap k w
fmapMaybe r f = inner where
  inner : a -> PrefixMap k v -> PrefixMap k w
  inner z (MkPrefix c m) = MkPrefix (mapMaybe (f z) c) (imapMaybe (\i => nonNull . inner (r z i)) m)

fwither : (Applicative t, Ord k) => (r : a -> k -> a) -> (f : a -> v -> t (Maybe w)) -> (z : a) -> PrefixMap k v -> t (PrefixMap k w)
fwither r f = inner where
  inner : a -> PrefixMap k v -> t (PrefixMap k w)
  inner z (MkPrefix c m) = MkPrefix <$> wither (f z) c <*> iwither (\i, n => nonNull <$> inner (r z i) n) m


public export
record FoldingIndex (k : Type) (z : accum) (r : accum -> k -> accum) (v : Type) where
  constructor FoldIndex
  unfoldIndex : PrefixMap k v

export
Functor (FoldingIndex k z r) where
  map f (FoldIndex m) = FoldIndex $ map f m

export
{z : a} -> {r : a -> k -> a} -> IndFunctor a (FoldingIndex k z r) where
  imap f (FoldIndex m) = FoldIndex $ fmap r f z m

export
Foldable (FoldingIndex k z r) where
  foldl f z (FoldIndex m) = foldl f z m
  foldr f z (FoldIndex m) = foldr f z m

export
{z : a} -> {r : a -> k -> a} -> IndFoldable a (FoldingIndex k z r) where
  ifoldl f u (FoldIndex m) = ffoldl r (flip f) u z m
  ifoldr f u (FoldIndex m) = ffoldr r f z m u
  iconcatMap f (FoldIndex m) = fconcatMap r f z m

export
Traversable (FoldingIndex k z r) where
  traverse f (FoldIndex m) = FoldIndex <$> traverse f m

export
{z : a} -> {r : a -> k -> a} -> IndTraversable a (FoldingIndex k z r) where
  itraverse f (FoldIndex m) = FoldIndex <$> ftraverse r f z m

export
Ord k => Filterable (FoldingIndex k z r) where
  mapMaybe f (FoldIndex m) = FoldIndex $ mapMaybe f m

export
{z : a} -> {r : a -> k -> a} -> Ord k => IndFilterable a (FoldingIndex k z r) where
  imapMaybe f (FoldIndex m) = FoldIndex $ fmapMaybe r f z m

export
Ord k => Witherable (FoldingIndex k z r) where
  wither f (FoldIndex m) = FoldIndex <$> wither f m

export
{z : a} -> {r : a -> k -> a} -> Ord k => IndWitherable a (FoldingIndex k z r) where
  iwither f (FoldIndex m) = FoldIndex <$> fwither r f z m
