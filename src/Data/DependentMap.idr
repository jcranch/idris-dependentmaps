module Data.DependentMap

import Control.Monad.Identity
import Decidable.Equality

import Data.Filterable.Dependent
import Data.Foldable.Dependent
import Data.Functor.Dependent
import Data.Traversable.Dependent
import Data.Witherable.Dependent
import Data.Withering.Dependent

import Data.DecOrd
import Data.Misc


-- Dependent sorted maps, implemented as size-balanced trees of the
-- Chen (2007) variety: each node is not to be smaller than either of
-- its sibling's children.


export
data DMap : (k : Type) -> (k -> Type) -> Type where
  Bin : Nat -> (x : k) -> v x -> DMap k v -> DMap k v -> DMap k v
  Tip : DMap k v

export
length : DMap k v -> Nat
length Tip = 0
length (Bin n _ _ _ _) = n

bin : (x : k) -> v x -> DMap k v -> DMap k v -> DMap k v
bin x a l r = Bin (length l + 1 + length r) x a l r

export
empty : DMap k v
empty = Tip

export
null : DMap k v -> Bool
null Tip = True
null _ = False

export
singleton : (x : k) -> v x -> DMap k v
singleton x a = Bin 1 x a Tip Tip

export
psingleton : DPair k v -> DMap k v
psingleton (MkDPair x a) = singleton x a

export
maybeSingleton : (x : k) -> Maybe (v x) -> DMap k v
maybeSingleton x (Just a) = singleton x a
maybeSingleton _ Nothing = empty

mutual
  -- Has the left half got too big?
  balanceL : DMap k v -> DMap k v
  balanceL t@(Bin n x5 a5 (Bin _ x1 a1 t0 (Bin m x3 a3 t2 t4)) t6) = if m > length t6
    then balance (Bin n x3 a3 (balanceL (bin x1 a1 t0 t2)) (balanceR (bin x5 a5 t4 t6)))
    else balanceL' t
  balanceL t = balanceL' t

  balanceL' : DMap k v -> DMap k v
  balanceL' t@(Bin n x3 a3 (Bin _ x1 a1 t0 t2) t4) = if length t0 > length t4
    then balance (Bin n x1 a1 t0 (balanceR (bin x3 a3 t2 t4)))
    else t
  balanceL' t = t

  -- Has the right half got too big?
  balanceR : DMap k v -> DMap k v
  balanceR t@(Bin n x1 a1 t0 (Bin _ x5 a5 (Bin m x3 a3 t2 t4) t6)) = if m > length t0
    then balance (Bin n x3 a3 (balanceL (bin x1 a1 t0 t2)) (balanceR (bin x5 a5 t4 t6)))
    else balanceR' t
  balanceR t = balanceR' t

  balanceR' : DMap k v -> DMap k v
  balanceR' t@(Bin n x1 a1 t0 (Bin _ x3 a3 t2 t4)) = if length t4 > length t0
    then balance (Bin n x3 a3 (balanceL (bin x1 a1 t0 t2)) t4)
    else t
  balanceR' t = t

  -- Has either half got too big?
  balance : DMap k v -> DMap k v
  balance = balanceL . balanceR

-- Not safe for general use; assumes all keys in the left argument
-- less than all keys in the right argument.
export
concatenate : Ord k => DMap k v -> DMap k v -> DMap k v
concatenate Tip m = m
concatenate m Tip = m
concatenate t1@(Bin n1 x1 a1 l1 r1) t2@(Bin n2 x2 a2 l2 r2) = if n1 > n2
  then balanceR $ Bin (n1+n2) x1 a1 l1 (concatenate r1 t2)
  else balanceL $ Bin (n1+n2) x2 a2 (concatenate t1 l2) r2

export
{0 k : Type} -> DepFunctor k (DMap k) where
  dmap _ Tip = Tip
  dmap f (Bin n x a l r) = Bin n x (f x a) (dmap f l) (dmap f r)

export
{0 k : Type} -> DepFoldable k (DMap k) where
  -- dfoldl : (f : m -> (x : k) -> v x -> m) -> m -> DMap k v -> m
  dfoldl _ z Tip = z
  dfoldl f z (Bin _ y a l r) = dfoldl f (f (dfoldl f z l) y a) r

  --dfoldr : (f : (x : k) -> v x -> m -> m) -> m -> DMap k v -> m
  dfoldr _ z Tip = z
  dfoldr f z (Bin _ y a l r) = dfoldr f (f y a (dfoldr f z r)) l

  -- dconcatMap : Monoid m => (f : (x : k) -> v x -> m) -> DMap k v -> m
  dconcatMap f Tip = neutral
  dconcatMap f (Bin _ y a l r) = dconcatMap f l <+> f y a <+> dconcatMap f r

export
{0 k : Type} -> DepTraversable k (DMap k) where
  dtraverse _ Tip = pure Tip
  dtraverse f (Bin n y a l r) = Bin n y <$> f y a <*> dtraverse f l <*> dtraverse f r

export
{0 k : Type} -> (Ord k) => DepFilterable k (DMap k) where
  dmapMaybe _ Tip = Tip
  dmapMaybe f (Bin n y a l r) = case f y a of
    Just b => (dmapMaybe f l `concatenate` singleton y b) `concatenate` dmapMaybe f r
    Nothing => dmapMaybe f l `concatenate` dmapMaybe f r

export
{0 k : Type} -> (Ord k) => DepWitherable k (DMap k) where

export
basicLookup : Ord k => (x : k) -> {0 v : k -> Type} -> DMap k v -> Maybe (DPair k v)
basicLookup _ Tip = Nothing
basicLookup x (Bin _ y a l r) = case compare x y of
  LT => basicLookup x l
  GT => basicLookup x r
  EQ => Just $ MkDPair y a

export
lookup : (DecEq k, Ord k) => (x : k) -> {0 v : k -> Type} -> DMap k v -> Maybe (v x)
lookup x m = fromDPair {v = v} x =<< basicLookup x m

-- Insert, and also return the old key. This is actually efficient,
-- since it minimises useless rebalancing.
export
basicReplace : Ord k => (x : k) -> v x -> DMap k v -> (Maybe (DPair k v), DMap k v)
basicReplace x a Tip = (Nothing, singleton x a)
basicReplace x a (Bin n y b l r) = case compare x y of
  LT => let
    (f, l') = basicReplace x a l
    in case f of
      Just _ => (f, Bin n y b l' r)
      Nothing => (f, balanceL (Bin (n+1) y b l' r))
  GT => let
    (f, r') = basicReplace x a r
    in case f of
      Just _ => (f, Bin n y b l r')
      Nothing => (f, Bin n y b l r')
  EQ => (Just (MkDPair y b), Bin n x a l r)

export
replace : (DecEq k, Ord k) => (x : k) -> v x -> DMap k v -> (Maybe (v x), DMap k v)
replace x a m = let
  (f, n) = basicReplace x a m
  in (fromDPair {v = v} x =<< f, n)

export
insert : (Ord k) => (x : k) -> v x -> DMap k v -> DMap k v
insert x a = snd . basicReplace x a

-- splits the map into keys less than x and keys greater than x;
-- avoids using DecEq
export
splitAround : (Ord k) => (x : k) -> {0 v : k -> Type} -> DMap k v -> (DMap k v, Bool, DMap k v)
splitAround _ Tip = (Tip, False, Tip)
splitAround x (Bin _ y b l r) = case compare x y of
  LT => let
    (u, f, v) = splitAround x l
    in (u, f, balanceR (bin y b v r))
  GT => let
    (u, f, v) = splitAround x r
    in (balanceL (bin y b l u), f, v)
  EQ => (l, True, r)

export
basicSplitAt : (Ord k) => (x : k) -> {0 v : k -> Type} -> DMap k v -> (DMap k v, Maybe (DPair k v), DMap k v)
basicSplitAt _ Tip = (Tip, Nothing, Tip)
basicSplitAt x (Bin _ y b l r) = case compare x y of
  LT => let
    (u, m, v) = basicSplitAt x l
    in (u, m, balanceR (bin y b v r))
  GT => let
    (u, m, v) = basicSplitAt x r
    in (balanceL (bin y b u l), m, v)
  EQ => (l, Just (MkDPair y b), r)

export
splitAt : (DecEq k, Ord k) => (x : k) -> {0 v : k -> Type} -> DMap k v -> (DMap k v, Maybe (v x), DMap k v)
splitAt x m = let
  (l, f, r) = basicSplitAt x m
  in (l, fromDPair {v = v} x =<< f, r)

export
delete : Ord k => (x : k) -> DMap k v -> DMap k v
delete x m = let
  (l, f, r) = splitAround x m
  in if f then concatenate l r else m

||| Remove element, providing it if present
export
basicExtract : (Ord k) => (x : k) -> DMap k v -> (Maybe (DPair k v), DMap k v)
basicExtract x m = let
  (l, a, r) = basicSplitAt x m
  in case a of
    Just _ => (a, concatenate l r)
    Nothing => (Nothing, m)

export
extract : (DecEq k, Ord k) => (x : k) -> DMap k v -> (Maybe (v x), DMap k v)
extract x m = let
  (f, n) = basicExtract x m
  in (fromDPair x =<< f, n)

||| This function, while general, is risky: users must guarantee that
||| the replacement keypair they provide will have the same key.
export
basicAlterF : (Functor f, Ord k) => (x : k) -> (Maybe (DPair k v) -> f (Maybe (DPair k v))) -> DMap k v -> f (DMap k v)
basicAlterF x g = map snd . inner where
  inner : DMap k v -> f (Maybe Bool, DMap k v)
  inner Tip = (\m => case m of
      Nothing => (Nothing, Tip)
      (Just a) => (Just True, psingleton a)) <$> g Nothing
  inner (Bin n y a l r) = case compare x y of
    LT => (\t => case t of
      (Nothing, l') => (Nothing, Bin n y a l' r)
      (Just True, l') => (Just True, balanceL $ Bin (n+1) y a l' r)
      (Just False, l') => (Just False, balanceR $ bin y a l' r)) <$> inner l
    GT => (\t => case t of
      (Nothing, r') => (Nothing, Bin n y a l r')
      (Just True, r') => (Just True, balanceR $ Bin (n+1) y a l r')
      (Just False, r') => (Just False, balanceL $ bin y a l r')) <$> inner r
    EQ => (\t => case t of
      Nothing => (Just False, concatenate l r)
      (Just (MkDPair z b)) => (Nothing, Bin n z b l r)) <$> g (Just (MkDPair y a))


export
basicAlter : (Ord k) => (x : k) -> (Maybe (DPair k v) -> Maybe (DPair k v)) -> DMap k v -> DMap k v
basicAlter x f = runIdentity . basicAlterF x (pure . f)


export
alterF : (Functor f, DecEq k, Ord k) => (x : k) -> (Maybe (v x) -> f (Maybe (v x))) -> DMap k v -> f (DMap k v)
alterF x g = basicAlterF x (map (map (MkDPair x)) . g . (fromDPair x =<<))


export
alter : (DecEq k, Ord k) => (x : k) -> (Maybe (v x) -> Maybe (v x)) -> DMap k v -> DMap k v
alter x g = basicAlter x (map (MkDPair x) . g . (fromDPair x =<<))


-- This merge does not assume DecEq, but one can assume that onBoth
-- will be only run when x = x'.
export
mergeA : (Applicative f, Ord k)
      => DepWithering f k u w
      -> DepWithering f k v w
      -> ((x, y : k) -> u x -> v y -> f (Maybe (w x)))
      -> DMap k u
      -> DMap k v
      -> f (DMap k w)
mergeA onLeft onRight onBoth = inner where
  inner : DMap k u -> DMap k v -> f (DMap k w)
  inner Tip m = runDepWither onRight m
  inner m Tip = runDepWither onLeft m
  inner (Bin _ x a l r) m = let
    (l', t, r') = basicSplitAt x m
    c = maybeSingleton x <$> case t of
      Nothing => depWitherOne onLeft x a
      Just (y ** b) => onBoth x y a b
    in concatenate <$> inner l l' <*> (concatenate <$> c <*> inner r r')

merge : (Ord k)
     => DepWithering Identity k u w
     -> DepWithering Identity k v w
     -> ((x, y : k) -> u x -> v y -> Maybe (w x))
     -> DMap k u
     -> DMap k v
     -> DMap k w
merge onLeft onRight onBoth m1 m2 = runIdentity $ mergeA onLeft onRight (\x, y, a, b => Id $ onBoth x y a b) m1 m2

||| Union of maps.
||| Prefers the values in the second argument.
export
union : Ord k => {0 v : k -> Type} -> DMap k v -> DMap k v -> DMap k v
union m1 m2 = merge preserving preserving (\_, _, x, _ => Just x) m2 m1

public export
Ord k => Semigroup (DMap k v) where
  (<+>) = union

public export
Ord k => Monoid (DMap k v) where
  neutral = Tip

export
fromList : (Ord k, Foldable t) => t (DPair k v) -> DMap k v
fromList = foldl (\m, (MkDPair x a) => insert x a m) neutral

export
toList : DMap k v -> List (DPair k v)
toList = dfoldr (\x, a, l => MkDPair x a::l) []

export
minView : DMap k v -> Maybe (DPair k v, DMap k v)
minView Tip = Nothing
minView (Bin _ x a l r) = Just $ case minView l of
  Just (m, l') => (m, balanceR (bin x a l' r))
  Nothing => (MkDPair x a, r)

export
maxView : DMap k v -> Maybe (DMap k v, DPair k v)
maxView Tip = Nothing
maxView (Bin _ x a l r) = Just $ case maxView r of
  Just (r', m) => (balanceL (bin x a l r'), m)
  Nothing => (l, MkDPair x a)

||| If the map is a singleton, return it as a DPair
export
singletonView : DMap k v -> Maybe (DPair k v)
singletonView (Bin _ x a Tip Tip) = Just (MkDPair x a)
singletonView _ = Nothing


-- A foldable wrapper providing access to keys
public export
data Keys : Type -> Type where
  KeyView : {k : Type} -> {v : k -> Type} -> DMap k v -> Keys k

export
Foldable Keys where
  foldr f z (KeyView m) = dfoldr (\x, _, e => f x e) z m
  foldl f z (KeyView m) = dfoldl (\e, x, _ => f e x) z m


-- One day Idris should perhaps be able to compose the standard list
-- equality with eqDPairFromDec automatically, but I haven't been able
-- to get it to do that. So, until then...
[listDPairEq] {0 v : k -> Type} -> (DecEq k, {x : k} -> Eq (v x)) => Eq (List (DPair k v)) where
  [] == [] = True
  x :: xs == y :: ys = ((==) @{eqDPairFromDec} x y) && xs == ys
  _ == _ = False

export
[eqDMapFromDec] {0 v : k -> Type} -> (DecEq k, {x : k} -> Eq (v x)) => Eq (DMap k v) where
  a == b = (==) @{listDPairEq} (toList a) (toList b)


||| A variant of alterF that assumes the key will be present before and after
export
changeF : (Functor f, DecEq k, Ord k) => {0 v : k -> Type} -> (x : k) -> (v x -> f (v x)) -> DMap k v -> f (DMap k v)
changeF x g = assert_total $ let
  h : Maybe (v x) -> f (Maybe (v x))
  h Nothing = idris_crash "changeF: expected to find this key"
  h (Just a) = Just <$> g a
  in alterF x h


||| A variant of alter that assumes the key will be present before and after
export
change : (DecEq k, Ord k) => {0 v : k -> Type} -> (x : k) -> (v x -> v x) -> DMap k v -> DMap k v
change x g = assert_total $ let
  h : Maybe (v x) -> Maybe (v x)
  h Nothing = idris_crash "change: expected to find this key"
  h (Just a) = Just (g a)
  in alter x h



{-
-- Haven't managed to get this working yet
public export
data HasKey : DMap k v -> k -> Type where
  HasKeyL : HasKey l z -> HasKey (Bin n x a l r) z
  HasKeyR : HasKey r z -> HasKey (Bin n x a l r) z
  HasKeyM : (x : k) -> HasKey (Bin n x a l r) x


public export
data Ordered : (o : k -> k -> Type) -> DMap k v -> Type where
  TipOrdered : Ordered o Tip
  BinOrdered : (HasKey l y -> o y x) -> (HasKey r z -> o x z) -> Ordered o (Bin n x a l r)
-}

{-
||| If we can inspect evidence that a key is present, can look it up
hasBasicLookup : (h : HasKey m z) -> DPair k v
hasBasicLookup (HasKeyM x a) = MkDPair x a
hasBasicLookup (HasKeyL h) = hasBasicLookup h
hasBasicLookup (HasKeyR h) = hasBasicLookup h

-- Want a more cunning version of that where we don't inspect the
-- HasKey but deduce something from it existing (and do inspect the map)
-}


{-

||| Keys are present after inserting them
insertHasHere : (x : k) -> (a : v x) -> (m : DMap k v) -> HasKey (insert x a m) z
insertHasHere x a Tip = HasKeyM x a
insertHasHere x a (Bin n y b l r) = case x y of
  LT => ?what
  GT => ?which
  EQ => HasKeyM x a

||| Keys are preserved by insertions
insertHasThere : HasKey m z -> HasKey (insert x y m) z
insertHasThere
-}

-- Can use HasKey -> Void for HasntKey
