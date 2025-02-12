module Data.DependentMap

import Decidable.Equality

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

export
dmap : ((x : k) -> u x -> v x) -> DMap k u -> DMap k v
dmap _ Tip = Tip
dmap f (Bin n x a l r) = Bin n x (f x a) (dmap f l) (dmap f r)

export
lookup : (DecEq k, Ord k) => (x : k) -> {0 v : k -> Type} -> DMap k v -> Maybe (v x)
lookup _ Tip = Nothing
lookup x (Bin _ y a l r) = case compare x y of
  LT => lookup x l
  GT => lookup x r
  EQ => fromDPair {v = v} x (MkDPair y a)

export
singleton : (x : k) -> v x -> DMap k v
singleton x a = Bin 1 x a Tip Tip

-- Insert, and also return True if key was new; false if key was
-- replaced. This minimises useless rebalancing.
export
insertAndReport : Ord k => (x : k) -> v x -> DMap k v -> (Bool, DMap k v)
insertAndReport x a Tip = (True, singleton x a)
insertAndReport x a (Bin n y b l r) = case compare x y of
  LT => let
    (f, l') = insertAndReport x a l
    in if f
      then (True, balanceL (Bin (n+1) y b l' r))
      else (False, Bin n y b l' r)
  GT => let
    (f, r') = insertAndReport x a r
    in if f
      then (True, balanceR (Bin (n+1) y b l r'))
      else (False, Bin n y b l r')
  EQ => (False, Bin n x a l r)

export
insert : Ord k => (x : k) -> v x -> DMap k v -> DMap k v
insert x a t = snd $ insertAndReport x a t

-- splits the map into keys less than x and keys greater than x;
-- avoids using DecEq
export
splitAround : Ord k => (x : k) -> {0 v : k -> Type} -> DMap k v -> (DMap k v, Bool, DMap k v)
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
splitAt : (DecEq k, Ord k) => (x : k) -> {0 v : k -> Type} -> DMap k v -> (DMap k v, Maybe (v x), DMap k v)
splitAt _ Tip = (Tip, Nothing, Tip)
splitAt x (Bin _ y b l r) = case compare x y of
  LT => let
    (u, m, v) = splitAt x l
    in (u, m, balanceR (bin y b v r))
  GT => let
    (u, m, v) = splitAt x r
    in (balanceL (bin y b u l), m, v)
  EQ => (l, fromDPair {v = v} x (MkDPair y b), r)

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
delete : Ord k => (x : k) -> DMap k v -> DMap k v
delete x m = let
  (l, f, r) = splitAround x m
  in if f then concatenate l r else m

-- Remove element, providing it if present
export
extract : (DecEq k, Ord k) => (x : k) -> DMap k v -> (Maybe (v x), DMap k v)
extract x m = let
  (l, a, r) = splitAt x m
  in case a of
    Just _ => (a, concatenate l r)
    Nothing => (Nothing, m)

-- Prefers the values in the second argument
export
union : Ord k => {0 v : k -> Type} -> DMap k v -> DMap k v -> DMap k v
union m Tip = m
union m (Bin _ x a l r) = let
  (l', _, r') = splitAround x m
  in balance $ bin x a (union l' l) (union r' r)

public export
Ord k => Semigroup (DMap k v) where
  (<+>) = union

public export
Ord k => Monoid (DMap k v) where
  neutral = Tip

export
fromList : (Ord k, Foldable t) => t (DPair k v) -> DMap k v
fromList = foldl (\m, (MkDPair x a) => insert x a m) neutral

-- Dependent left fold
export
dfoldl : (f : m -> (x : k) -> v x -> m) -> m -> DMap k v -> m
dfoldl _ z Tip = z
dfoldl f z (Bin _ y a l r) = dfoldl f (f (dfoldl f z l) y a) r

-- Dependent right fold
export
dfoldr : (f : (x : k) -> v x -> m -> m) -> m -> DMap k v -> m
dfoldr _ z Tip = z
dfoldr f z (Bin _ y a l r) = dfoldr f (f y a (dfoldr f z r)) l

export
dconcatMap : Monoid m => (f : (x : k) -> v x -> m) -> DMap k v -> m
dconcatMap f Tip = neutral
dconcatMap f (Bin _ y a l r) = dconcatMap f l <+> f y a <+> dconcatMap f r

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


-- A foldable wrapper providing access to keys
public export
data Keys : (k : Type) -> Type where
  KeyView : DMap k v -> Keys k

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


{-
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
-}



public export
data HasKey : DMap k v -> k -> Type where
  HasKeyL : HasKey l z -> HasKey (Bin n x a l r) z
  HasKeyR : HasKey r z -> HasKey (Bin n x a l r) z
  HasKeyM : {0 a : k -> Type} -> (x : k) -> HasKey (Bin n x a l r) x

emptyHasntKey : HasKey Tip x -> Void
emptyHasntKey (HasKeyL y) impossible
emptyHasntKey (HasKeyR y) impossible
emptyHasntKey (HasKeyM y) impossible


public export
data Ordered : (o : k -> k -> Type) -> DMap k v -> Type where
  TipOrdered : Ordered o Tip
  BinOrdered : Ordered o l -> Ordered o r -> (HasKey l y -> o y x) -> (HasKey r z -> o x z) -> Ordered o (Bin n x a l r)

{-
singletonOrdered : TotalOrder a o => {x : a} -> {0 v : a -> Type} -> {y : v x} -> Ordered o (singleton x y)
singletonOrdered = BinOrdered TipOrdered TipOrdered ?x ?y
-}

{-







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
