||| Dependent sorted maps, implemented as "hairy finger trees": like
||| fingertrees, but with interspersed unpacked elements for easy
||| comparisons.
module Data.DependentMap

import Control.Monad.Identity
import Data.Nat
import Decidable.Equality

import Data.Witherable.Dependent
import Data.Withering.Dependent

import Control.Relation.TotalOrder
import Decidable.Ordering

import Data.Misc


-- Dependent sorted maps, implemented as size-balanced trees of the
-- Chen (2007) variety: each node is not to be smaller than either of
-- its sibling's children.
-- http://wcipeg.com/wiki/Size_Balanced_Tree


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
  balanceL t@(Bin j x5 a5 (Bin _ x1 a1 t0 (Bin i x3 a3 t2 t4)) t6) = if i > length t6
    then balance (Bin j x3 a3 (balanceL (bin x1 a1 t0 t2)) (balanceR (bin x5 a5 t4 t6)))
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

||| Concatenate two maps
|||
||| Unsafe, insofar as it assumes all keys in the left argument are
||| less than all keys in the right argument.
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
    Just b => balance (bin y b (dmapMaybe f l) (dmapMaybe f r))
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

-- Insert, and also return the old key. This is efficient, since it
-- prevents us rebalancing when the tree shape isn't changed.
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

||| splits the map into keys less than x and keys greater than x;
||| avoids using DecEq
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


public export
data HasKey : (0 k : Type) -> (0 v : k -> Type) -> DMap k v -> k -> Type where
  HasKeyL : HasKey k v l z -> HasKey k v (Bin n x a l r) z
  HasKeyR : HasKey k v r z -> HasKey k v (Bin n x a l r) z
  HasKeyM : (x : k) -> {0 a : v x} -> HasKey k v (Bin n x a l r) x


public export
emptyHasntKey : HasKey k v Tip x -> Void
emptyHasntKey (HasKeyL y) impossible
emptyHasntKey (HasKeyR y) impossible
emptyHasntKey (HasKeyM y) impossible

public export
singletonHasKey : (x : k) -> (y : v x) -> HasKey k v (singleton x y) x
singletonHasKey x y = HasKeyM x


mutual
  balanceHasKeyL : {m : DMap k v} -> HasKey k v m x -> HasKey k v (balanceL m) x
  balanceHasKeyL {m} h with (m)
    balanceHasKeyL {m} h | (Bin j x5 a5 (Bin _ x1 a1 t0 (Bin i x3 a3 t2 t4)) t6) with (i > length t6)
      balanceHasKeyL {m} h | (Bin j x5 a5 (Bin _ x1 a1 t0 (Bin i x3 a3 t2 t4)) t6) | True = balanceHasKey ?bl_rhs1
      balanceHasKeyL {m} h | (Bin j x5 a5 (Bin _ x1 a1 t0 (Bin i x3 a3 t2 t4)) t6) | False = ?bl_rhs2
    balanceHasKeyL {m} h | t = ?bl_rhs3 -- balanceHasKeyL' {m = t} h

  balanceHasKeyL' : {m : DMap k v} -> HasKey k v m x -> HasKey k v (balanceL' m) x
  balanceHasKeyL' = ?bl'

  balanceHasKeyR : {m : DMap k v} -> HasKey k v m x -> HasKey k v (balanceR m) x
  balanceHasKeyR = ?br

  balanceHasKeyR' : {m : DMap k v} -> HasKey k v m x -> HasKey k v (balanceR' m) x
  balanceHasKeyR' = ?br'

  balanceHasKey : {m : DMap k v} -> HasKey k v m x -> HasKey k v (balance m) x
  balanceHasKey {m} h = balanceHasKeyL {m = balanceR m} (balanceHasKeyR {m = m} h)
{-
-}


public export
data Ordered : (0 k : Type)
            -> (0 v : k -> Type)
            -> (o : k -> k -> Type)
            -> DMap k v
            -> Type where

  ||| The tip is always ordered
  TipOrdered : Ordered k v o Tip

  ||| A Bin is ordered if the left and right are ordered, and if the
  ||| centre is greater than every element on the left and less than
  ||| every element on the right.
  BinOrdered : Ordered k v o l
            -> ({y : k} -> HasKey k v l y -> o y x)
            -> Ordered k v o r
            -> ({z : k} -> HasKey k v r z -> o x z)
            -> Ordered k v o (Bin n x a l r)


||| Singletons are vacuously ordered (that is, without any assumptions
||| on the relation o).
public export
singletonOrdered : (0 k : Type)
                -> (0 v : k -> Type)
                -> {o : k -> k -> Type}
                -> (x : k)
                -> (y : v x)
                -> Ordered k v o (singleton x y)
singletonOrdered k v x y = BinOrdered TipOrdered (absurd . emptyHasntKey) TipOrdered (absurd . emptyHasntKey)


||| A Bin which has a key which is less than the root has it in the
||| left part
hasKeyL : TotalOrder k o
       => {x : k}
       -> {y : k}
       -> {z : v x}
       -> Ordered k v o (Bin n x z l r)
       -> HasKey k v (Bin n x z l r) y
       -> o y x
       -> HasKey k v l y
hasKeyL _ (HasKeyL h) _ = h
hasKeyL _ (HasKeyM _) c = absurd (irrefl c)
hasKeyL (BinOrdered _ _ _ p) (HasKeyR h) c = absurd (irrefl (transitive (p h) c))


||| A Bin which has a key which is less than the root has it in the
||| right part
hasKeyR : TotalOrder k o
       => {x : k}
       -> {y : k}
       -> {z : v x}
       -> Ordered k v o (Bin n x z l r)
       -> HasKey k v (Bin n x z l r) y
       -> o x y
       -> HasKey k v r y
hasKeyR (BinOrdered _ p _ _) (HasKeyL h) c = absurd (irrefl (transitive (p h) c))
hasKeyR _ (HasKeyM _) c = absurd (irrefl c)
hasKeyR _ (HasKeyR h) _ = h


{-
mutual
  balanceLOrdered : TotalOrder k o => (m : DMap k v) -> Ordered k v o m -> Ordered k v o (balanceL m)
  balanceLOrdered t@(Bin n x5 a5 (Bin _ x1 a1 t0 (Bin m x3 a3 t2 t4)) t6) p = if m > length t6
    then ?x -- balance (Bin n x3 a3 (balanceL (bin x1 a1 t0 t2)) (balanceR (bin x5 a5 t4 t6)))
    else ?y -- balanceL' t
  balanceLOrdered p = balanceLOrdered' p

  balanceLOrdered' : TotalOrder k o => (m : DMap k v) -> Ordered k v o m -> Ordered k v o (balanceL' m)

  balanceROrdered : TotalOrder k o => (m : DMap k v) -> Ordered k v o m -> Ordered k v o (balanceR m)

  balanceROrdered' : TotalOrder k o => (m : DMap k v) -> Ordered k v o m -> Ordered k v o (balanceR' m)

  balanceOrdered : TotalOrder k o => (m : DMap k v) -> Ordered k v o m -> Ordered k v o (balance m)
  balanceOrdered = ?w -- balanceLOrdered . balanceROrdered
-}


-- also want versions of "alter" etc

public export
hasKeyLookup : TotalOrder k o
            => (m : DMap k v)
            -> (p : Ordered k v o m)
            -> (x : k)
            -> (0 h : HasKey k v m x)
            -> v x
hasKeyLookup (Bin _ x' y l r) p x h with (trichotomy {r = o} x x')
  hasKeyLookup (Bin _ x' y _ _) _ x' _ | (EQ Refl) = y
  hasKeyLookup (Bin _ x' y l _) p@(BinOrdered q _ _ _) x h | (LT w) = hasKeyLookup l q x (hasKeyL p h w)
  hasKeyLookup (Bin _ x' y _ r) p@(BinOrdered _ _ q _) x h | (GT w) = hasKeyLookup r q x (hasKeyR p h w)
hasKeyLookup Tip _ _ (HasKeyL _) impossible
hasKeyLookup Tip _ _ (HasKeyR _) impossible
hasKeyLookup Tip _ _ (HasKeyM _) impossible


{-
||| Keys are present after inserting them
insertHasHere : (Ord k, DecOrd k o) => (x : k) -> (y : v x) -> (m : DMap k v) -> HasKey k v (insert x y m) x
insertHasHere x y Tip = HasKeyM x
insertHasHere x y (Bin n x' _ l r) with (decOrd {r = o} x x')
  insertHasHere x y (Bin n x' _ l r) | with_pat = ?what_rhs
-}

{-
||| Keys are preserved by insertions
insertHasThere : HasKey m z -> HasKey (insert x y m) z
insertHasThere
-}


lChildLength : DMap k v -> Nat
lChildLength Tip = 0
lChildLength (Bin _ _ _ l _) = length l

rChildLength : DMap k v -> Nat
rChildLength Tip = 0
rChildLength (Bin _ _ _ _ r) = length r


||| Expresses that the tree is balanced in the sense of Chen, and also
||| that the length count is correct
data Balanced : DMap k v -> Type where
  TipBalanced : Balanced Tip
  BinBalanced : LTE (lChildLength l) (length r)
             -> LTE (rChildLength l) (length r)
             -> LTE (lChildLength r) (length l)
             -> LTE (rChildLength r) (length l)
             -> Balanced l
             -> Balanced r
             -> Balanced (Bin (length l + 1 + length r) k v l r)

{-
balanced : Balanced l -> Balanced r -> Balanced (balance (Bin (length l + 1 + length r) k v l r))
balanced = ?b
-}
