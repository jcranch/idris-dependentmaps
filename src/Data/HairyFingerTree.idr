module Data.HairyFingerTree

import Decidable.Ordering


data Node : Type -> Type -> Type where
  Node2 : (y0 : y) -> (x1 : x) -> (y2 : y) -> Node x y
  Node3 : (y0 : y) -> (x1 : x) -> (y2 : y) -> (x3 : x) -> (y4 : y) -> Node x y


data Digit : Type -> Type -> Type where
  Digit1 : (x0 : x) -> (y1 : y) -> Digit x y
  Digit2 : (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> Digit x y


data HairyFingers : Type -> Type -> Type where
  Empty : HairyFingers x y
  Singleton : (x0 : x) -> (y1 : y) -> HairyFingers x y
  Deep : (l : Digit x y) -> (m : HairyFingers x (Node x y)) -> (r : Digit x y) -> HairyFingers x y


appendl : (x0 : x) -> (y1 : y) -> (u : HairyFingers x y) -> HairyFingers x y
appendl x0 y1 Empty = Singleton x0 y1
appendl x0 y1 (Singleton x2 y3) = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)
appendl x0 y1 (Deep (Digit1 x2 y3) m r) = Deep (Digit2 x0 y1 x2 y3) m r
appendl x0 y1 (Deep (Digit2 x2 y3 x4 y5) m r) = Deep (Digit1 x0 y1) (appendl x2 (Node2 y3 x4 y5) m) r

appendr : (u : HairyFingers x y) -> (x0 : x) -> (y1 : y) -> HairyFingers x y
appendr Empty x0 y1 = Singleton x0 y1
appendr (Singleton x0 y1) x2 y3 = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)
appendr (Deep l m (Digit1 x0 y1)) x2 y3 = Deep l m (Digit2 x0 y1 x2 y3)
appendr (Deep l m (Digit2 x0 y1 x2 y3)) x4 y5 = Deep l (appendr m x0 (Node2 y1 x2 y3)) (Digit1 x4 y5)

-- It's possible and maybe desirable to give a more efficient implementation
appendl2 : (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> (u : HairyFingers x y) -> HairyFingers x y
appendl2 x0 y1 x2 y3 t = appendl x0 y1 (appendl x2 y3 t)

-- It's possible and maybe desirable to give a more efficient implementation
appendr2 : (u : HairyFingers x y) -> (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> HairyFingers x y
appendr2 t x0 y1 x2 y3 = appendr (appendr t x0 y1) x2 y3

-- It's possible and maybe desirable to give a more efficient implementation
appendl3 : (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> (x4 : x) -> (y5 : y) -> (u : HairyFingers x y) -> HairyFingers x y
appendl3 x0 y1 x2 y3 x4 y5 t = appendl x0 y1 (appendl x2 y3 (appendl x4 y5 t))

-- It's possible and maybe desirable to give a more efficient implementation
appendr3 : (u : HairyFingers x y) -> (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> (x4 : x) -> (y5 : y) -> HairyFingers x y
appendr3 t x0 y1 x2 y3 x4 y5 = appendr (appendr (appendr t x0 y1) x2 y3) x4 y5


concat2 : (u : HairyFingers x y) -> (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> (v : HairyFingers x y) -> HairyFingers x y
concat2 t1 x0 y1 x2 y3 Empty = appendr2 t1 x0 y1 x2 y3
concat2 Empty x0 y1 x2 y3 t2 = appendl2 x0 y1 x2 y3 t2
concat2 (Singleton x0 y1) x2 y3 x4 y5 t2 = appendl3 x0 y1 x2 y3 x4 y5 t2
concat2 t1 x0 y1 x2 y3 (Singleton x4 y5) = appendr3 t1 x0 y1 x2 y3 x4 y5
concat2 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 x4 y5 (Deep (Digit1 x6 y7) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2
concat2 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 x4 y5 (Deep (Digit2 x6 y7 x8 y9) m2 r2) = Deep l1 (concat2 m1 x0 (Node3 y1 x2 y3 x4 y5) x6 (Node2 y7 x8 y9) m2) r2
concat2 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 x6 y7 (Deep (Digit1 x8 y9) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node3 y5 x6 y7 x8 y9) m2) r2
concat2 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 x6 y7 (Deep (Digit2 x8 y9 xa yb) m2 r2) = Deep l1 (concat2 m1 x0 (Node3 y1 x2 y3 x4 y5) x6 (Node3 y7 x8 y9 xa yb) m2) r2

concat1 : (u : HairyFingers x y) -> (x0 : x) -> (y1 : y) -> (v : HairyFingers x y) -> HairyFingers x y
concat1 t1 x1 y2 Empty = appendr t1 x1 y2
concat1 Empty x1 y2 t2 = appendl x1 y2 t2
concat1 (Singleton x0 y1) x2 y3 t2 = appendl2 x0 y1 x2 y3 t2
concat1 t1 x0 y1 (Singleton x2 y3) = appendr2 t1 x0 y1 x2 y3
concat1 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 (Deep (Digit1 x4 y5) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat1 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 (Deep (Digit2 x4 y5 x6 y7) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2
concat1 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 (Deep (Digit1 x6 y7) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2
concat1 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 (Deep (Digit2 x6 y7 x8 y9) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node3 y5 x6 y7 x8 y9) m2) r2

concat : (u : HairyFingers x y) -> (v : HairyFingers x y) -> HairyFingers x y
concat t1 Empty = t1
concat Empty t2 = t2
concat (Singleton x0 y1) (Singleton x2 y3) = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)
concat (Singleton x0 y1) t2 = appendl x0 y1 t2
concat t1 (Singleton x1 y0) = appendr t1 x1 y0
concat (Deep l1 m1 (Digit1 x0 y1)) (Deep (Digit1 x2 y3) m2 r2) = Deep l1 (concat1 m1 x0 (Node2 y1 x2 y3) m2) r2
concat (Deep l1 m1 (Digit1 x0 y1)) (Deep (Digit2 x2 y3 x4 y5) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat (Deep l1 m1 (Digit2 x0 y1 x2 y3)) (Deep (Digit1 x4 y5) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat (Deep l1 m1 (Digit2 x0 y1 x2 y3)) (Deep (Digit2 x4 y5 x6 y7) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2


maybeSingleton : (m : Maybe (x, y)) -> HairyFingers x y
maybeSingleton Nothing = Empty
maybeSingleton (Just (x,y)) = Singleton x y


digitToTree : (d : Digit x y) -> HairyFingers x y
digitToTree (Digit1 x0 y1) = Singleton x0 y1
digitToTree (Digit2 x0 y1 x2 y3) = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)

maybeDigitToTree : Maybe (Digit x y) -> HairyFingers x y
maybeDigitToTree Nothing = Empty
maybeDigitToTree (Just d) = digitToTree d



-- Could just implement lookup as adjust, valued in a constant functor

interface HasLookup (0 a : Type) (0 v : a -> Type) (t : Type) where
  adjust : Functor f => (k : a) -> (v k -> f (v k)) -> t -> Maybe (f t)
  lookup : (k : a) -> t -> Maybe (v k)

interface HasNavigate (0 a : Type) (0 v : a -> Type) (t : Type) where
  ||| The meaning of `Either Bool z` in the type signature as follows:
  ||| * Right a is a successful lookup
  ||| * Left True indicates that the key is to be looked for further to the left
  ||| * Left False indicates that the key is not to be looked for further to the left
  adjust' : Functor f => (k : a) -> (v k -> f (v k)) -> t -> Either Bool (f t)
  navigate : (k : a) -> t -> Either Bool (v k)

fromLookup : Maybe x -> Either Bool x
fromLookup (Just a) = Right a
fromLookup Nothing = Left False

{x : Type} -> {y : Type} -> (HasNavigate a v x, HasLookup a v y) => HasLookup a v (Node x y) where
  lookup k (Node2 y0 x1 y2) = case navigate k x1 of
    Right a => Just a
    Left True => lookup k y0
    Left False => lookup k y2
  lookup k (Node3 y0 x1 y2 x3 y4) = case navigate k x3 of
    Right a => Just a
    Left True => case navigate k x1 of
      Right a => Just a
      Left True => lookup k y0
      Left False => lookup k y2
    Left False => lookup k y4
  adjust k f (Node2 y0 x1 y2) = case adjust' k f x1 of
    Right a => Just ((\z => Node2 y0 z y2) <$> a)
    Left True => map (\z => Node2 z x1 y2) <$> adjust k f y0
    Left False => map (\z => Node2 y0 x1 z) <$> adjust k f y2
  adjust k f (Node3 y0 x1 y2 x3 y4) = case adjust' k f x3 of
    Right a => Just ((\z => Node3 y0 x1 y2 z y4) <$> a)
    Left True => case adjust' k f x1 of
      Right a => Just ((\z => Node3 y0 z y2 x3 y4) <$> a)
      Left True => map (\z => Node3 z x1 y2 x3 y4) <$> adjust k f y0
      Left False => map (\z => Node3 y0 x1 z x3 y4) <$> adjust k f y2
    Left False => map (\z => Node3 y0 x1 y2 x3 z) <$> adjust k f y4

{x : Type} -> {y : Type} -> (HasNavigate a v x, HasLookup a v y) => HasNavigate a v (Digit x y) where
  navigate k (Digit1 x0 y1) = case navigate k x0 of
    Right a => Right a
    Left True => Left True
    Left False => fromLookup (lookup k y1)
  navigate k (Digit2 x0 y1 x2 y3) = case navigate k x2 of
    Right a => Right a
    Left True => case navigate k x0 of
      Right a => Right a
      Left True => Left True
      Left False => fromLookup (lookup k y1)
    Left False => fromLookup (lookup k y3)
  adjust' k f (Digit1 x0 y1) = case adjust' k f x0 of
    Right a => Right ((\z => Digit1 z y1) <$> a)
    Left True => Left True
    Left False => map (\z => Digit1 x0 z) <$> fromLookup (adjust k f y1)
  adjust' k f (Digit2 x0 y1 x2 y3) = case adjust' k f x2 of
    Right a => Right ((\z => Digit2 x0 y1 z y3) <$> a)
    Left True => case adjust' k f x0 of
      Right a => Right ((\z => Digit2 z y1 x2 y3) <$> a)
      Left True => Left True
      Left False => map (\z => Digit2 x0 z x2 y3) <$> fromLookup (adjust k f y1)
    Left False => map (\z => Digit2 x0 y1 x2 z) <$> fromLookup (adjust k f y3)

{x : Type} -> {y : Type} -> (HasNavigate a v x, HasLookup a v y) => HasNavigate a v (HairyFingers x y) where
  navigate k Empty = Left True
  navigate k (Singleton x0 y1) = case navigate k x0 of
    Right a => Right a
    Left True => Left True
    Left False => fromLookup (lookup k y1)
  navigate k (Deep l m r) = case navigate k r of
    Right a => Right a
    Left False => Left False
    Left True => case navigate k m of
      Right a => Right a
      Left False => Left False
      Left True => navigate k l
  adjust' k f Empty = Left True
  adjust' k f (Singleton x0 y1) = case adjust' k f x0 of
    Right a => Right ((\z => Singleton z y1) <$> a)
    Left True => Left True
    Left False => map (\z => Singleton x0 z) <$> fromLookup (adjust k f y1)
  adjust' k f (Deep l m r) = case adjust' k f r of
    Right a => Right ((\z => Deep l m z) <$> a)
    Left False => Left False
    Left True => case adjust' k f m of
      Right a => Right ((\z => Deep l z r) <$> a)
      Left False => Left False
      Left True => map (\z => Deep z m r) <$> adjust' k f l


{x : Type} -> HasNavigate a v x => HasLookup a v x where
  lookup k t = case navigate k t of
    Right a => Just a
    Left _ => Nothing
  adjust k f t = case adjust' k f t of
    Right a => Just a
    Left _ => Nothing

{x : Type} -> {o : x -> x -> Type} -> {v : x -> Type} -> (d : DecOrd x o) => HasNavigate x v (DPair x v) where
  navigate k (MkDPair a b) with (decOrd @{d} k a) | (compare k a)
    navigate k (MkDPair a b) | LT _    | LT = Left False
    navigate a (MkDPair a b) | EQ Refl | EQ = Right b
    navigate k (MkDPair a b) | GT _    | GT = Left True
  adjust' k f (MkDPair a b) with (decOrd @{d} k a) | (compare k a)
    adjust' k _ (MkDPair a b) | LT _    | LT = Left False
    adjust' a f (MkDPair a b) | EQ Refl | EQ = Right (MkDPair a <$> f b)
    adjust' k _ (MkDPair a b) | GT _    | GT = Left True



mutual
  deepNoL : HairyFingers x (Node x y) -> Digit x y -> HairyFingers x y
  deepNoL m r = let
    h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
    h x0 (Node2 y1 x2 y3) = (Digit2 x0 y1 x2 y3, Nothing)
    h x0 (Node3 y1 x2 y3 x4 y5) = (Digit1 x0 y1, Just (x2, Node2 y3 x4 y5))
    in case alterl h m of
      Nothing => digitToTree r
      Just (l, m') => Deep l m' r

  ||| A lens on the leftmost element (if it exists)
  alterl : (Functor f) => (x -> y -> f (Maybe (x, y))) -> HairyFingers x y -> Maybe (f (HairyFingers x y))
  alterl _ Empty = Nothing
  alterl f (Singleton x0 y1) = Just (maybeSingleton <$> f x0 y1)
  alterl f (Deep (Digit1 x0 y1) m r) = let
    g : Maybe (x, y) -> HairyFingers x y
    g (Just (x0', y1')) = Deep (Digit1 x0' y1') m r
    g Nothing = deepNoL m r
    in Just (g <$> f x0 y1)
  alterl f (Deep (Digit2 x0 y1 x2 y3) m r) = let
    g : Maybe (x, y) -> Digit x y
    g Nothing = Digit1 x2 y3
    g (Just (x0', y1')) = Digit2 x0' y1' x2 y3
    in Just ((\z => Deep z m r) . g <$> f x0 y1)

-- Could just implement this in terms of alterl with a constant functor
viewl : HairyFingers x y -> Maybe (x, y, HairyFingers x y)
viewl Empty = Nothing
viewl (Singleton x0 y1) = Just (x0, y1, Empty)
viewl (Deep (Digit1 x0 y1) m r) = let
  h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
  h x0 (Node2 y1 x2 y3) = (Digit2 x0 y1 x2 y3, Nothing)
  h x0 (Node3 y1 x2 y3 x4 y5) = (Digit1 x0 y1, Just (x2, Node2 y3 x4 y5))
  in Just . (x0,y1,) $ case alterl h m of
    Nothing => digitToTree r
    Just (l, m') => Deep l m' r
viewl (Deep (Digit2 x0 y1 x2 y3) m r) = Just (x0, y1, Deep (Digit1 x2 y3) m r)


mutual
  deepNoR : Digit x y -> HairyFingers x (Node x y) -> HairyFingers x y
  deepNoR l m = let
    h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
    h x0 (Node2 y1 x2 y3) = (Digit2 x0 y1 x2 y3, Nothing)
    h x0 (Node3 y1 x2 y3 x4 y5) = (Digit1 x4 y5, Just (x0, Node2 y1 x2 y3))
    in case alterr h m of
      Nothing => digitToTree l
      Just (r, m') => Deep l m r

  ||| A lens on the rightmost element (if it exists)
  alterr : (Functor f) => (x -> y -> f (Maybe (x, y))) -> HairyFingers x y -> Maybe (f (HairyFingers x y))
  alterr _ Empty = Nothing
  alterr f (Singleton x0 y1) = Just (maybeSingleton <$> f x0 y1)
  alterr f (Deep l m (Digit1 x0 y1)) = let
    g : Maybe (x, y) -> HairyFingers x y
    g (Just (x0', y1')) = Deep l m (Digit1 x0' y1')
    g Nothing = deepNoR l m
    in Just (g <$> f x0 y1)
  alterr f (Deep l m (Digit2 x0 y1 x2 y3)) = let
    g : Maybe (x, y) -> Digit x y
    g Nothing = Digit1 x0 y1
    g (Just (x2', y3')) = Digit2 x0 y1 x2' y3'
    in Just (Deep l m . g <$> f x2 y3)

-- Could just implement this in terms of alterr with a constant functor
viewr : HairyFingers x y -> Maybe (HairyFingers x y, x, y)
viewr Empty = Nothing
viewr (Singleton x0 y1) = Just (Empty, x0, y1)
viewr (Deep l m (Digit1 x0 y1)) = let
  h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
  h x0 (Node2 y1 x2 y3) = (Digit2 x0 y1 x2 y3, Nothing)
  h x0 (Node3 y1 x2 y3 x4 y5) = (Digit1 x4 y5, Just (x0, Node2 y1 x2 y3))
  in Just . (,x0,y1) $ case alterl h m of
    Nothing => digitToTree l
    Just (r, m') => Deep l m' r
viewr (Deep l m (Digit2 x0 y1 x2 y3)) = Just (Deep l m (Digit1 x0 y1), x2, y3)


||| This implementation packs nodes fairly tightly: given a long list
||| most nodes will be node3.
fromList : List (x,y) -> HairyFingers x y
fromList = let

  inner : (x,y) -> List (x,y) -> (Digit x y, List (x, Node x y))
  inner (x1,y2) [] = (Digit1 x1 y2, [])
  inner (x1,y2) [(x3,y4)] = (Digit2 x1 y2 x3 y4, [])
  inner (x1,y2) [(x3,y4),(x5,y6)] = (Digit1 x5 y6, [(x1, Node2 y2 x3 y4)])
  inner (x1,y2) ((x3,y4)::(x5,y6)::p::l) = ((x1, Node3 y2 x3 y4 x5 y6)::) <$> inner p l

  go : List (x,y) -> HairyFingers x y
  go [] = Empty
  go [(x1,y2)] = Singleton x1 y2
  go ((x1,y2)::p::t) = let
    (r,m) = inner p t
    in Deep (Digit1 x1 y2) (fromList m) r

  in go



deepMaybeL : Maybe (Digit x y) -> HairyFingers x (Node x y) -> Digit x y -> HairyFingers x y
deepMaybeL Nothing m r = deepNoL m r
deepMaybeL (Just l) m r = Deep l m r

deepMaybeR : Digit x y -> HairyFingers x (Node x y) -> Maybe (Digit x y) -> HairyFingers x y
deepMaybeR l m Nothing = deepNoR l m
deepMaybeR l m (Just r) = Deep l m r

-- Should we test the left half first in the case of a digit2?
splitDigit : (x -> Ordering) -> (y -> Ordering) -> Digit x y -> Either Bool (Maybe (Digit x y), Maybe (x,y), Maybe (Digit x y))
splitDigit f g (Digit1 x0 y1) = case f x0 y1 of
  LT => Left True
  EQ => Right (Nothing, Just (x0, y1), Nothing)
  GT => Left False
splitDigit f g (Digit2 x0 y1 x2 y3) = case f x2 y3 of
  LT => case f x0 y1 of
    LT => Left True
    EQ => Right (Nothing, Just (x0, y1), Just (Digit1 x2 y3))
    GT => Right (Just (Digit1 x0 y1), Nothing, Just (Digit1 x2 y3))
  EQ => Right (Just (Digit1 x0 y1), Just (x2, y3), Nothing)
  GT => Left False

-- This function sucks, in that we're descending into the structure twice.
nodeSearch : (x -> y -> Ordering) -> x -> Node x y -> Ordering
nodeSearch f x0 (Node2 y1 x2 y3) = case f x0 y1 of
  LT => LT
  EQ => EQ
  GT => ?ns_0
nodeSearch f x0 (Node3 y1 x2 y3 x4 y5) = ?ns_1

splitNavigate : (x -> y -> Ordering) -> HairyFingers x y -> Either Bool (HairyFingers x y, Maybe (x,y), HairyFingers x y)
splitNavigate f Empty = Left True
splitNavigate f (Singleton x0 y1) = case f x0 y1 of
  LT => Left True
  EQ => Right (Empty, Just (x0, y1), Empty)
  GT => Left False
splitNavigate f (Deep l m r) = case splitDigit f r of
  Right (t1, u, t2) => Right (deepMaybeR l m t1, u, maybeDigitToTree t2)
  Left False => Left False
  Left True => case splitNavigate (nodeSearch f) m of
    Right (t1, u, t2) => ?sn
    Left False => Right (deepNoR l m, Nothing, digitToTree r)
    Left True => case splitDigit f l of
      Right (t1, u, t2) => Right (maybeDigitToTree t1, u, deepMaybeL t2 m r)
      Left False => Right (digitToTree l, Nothing, deepNoL m r)
      Left True => Left True

split : (x -> y -> Ordering) -> HairyFingers x y -> (HairyFingers x y, Maybe (x,y), HairyFingers x y)
split f t = case splitNavigate f t of
  Right a => a
  Left True => (Empty, Nothing, t)
  Left False => (t, Nothing, Empty)
