module Data.HairyFingerTree


data Node : Type -> Type -> Type where
  Node2 : y -> x -> y -> Node x y
  Node3 : y -> x -> y -> x -> y -> Node x y


data Digit : Type -> Type -> Type where
  Digit1 : x -> y -> Digit x y
  Digit2 : x -> y -> x -> y -> Digit x y


data HairyFingers : Type -> Type -> Type where
  Empty : HairyFingers x y
  Singleton : x -> y -> HairyFingers x y
  Deep : Digit x y -> HairyFingers x (Node x y) -> Digit x y -> HairyFingers x y

appendl : x -> y -> HairyFingers x y -> HairyFingers x y
appendl x0 y1 Empty = Singleton x0 y1
appendl x0 y1 (Singleton x2 y3) = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)
appendl x0 y1 (Deep (Digit1 x2 y3) m r) = Deep (Digit2 x0 y1 x2 y3) m r
appendl x0 y1 (Deep (Digit2 x2 y3 x4 y5) m r) = Deep (Digit1 x0 y1) (appendl x2 (Node2 y3 x4 y5) m) r

appendr : HairyFingers x y -> x -> y -> HairyFingers x y
appendr Empty x1 y0 = Singleton x1 y0
appendr (Singleton x3 y2) x1 y0 = Deep (Digit1 x3 y2) Empty (Digit1 x1 y0)
appendr (Deep l m (Digit1 x3 y2)) x1 y0 = Deep l m (Digit2 x3 y2 x1 y0)
appendr (Deep l m (Digit2 x5 y4 x3 y2)) x1 y0 = Deep l (appendr m x5 (Node2 y4 x3 y2)) (Digit1 x1 y0)

-- It's possible and maybe desirable to give a more efficient implementation
appendl2 : x -> y -> x -> y -> HairyFingers x y -> HairyFingers x y
appendl2 x0 y1 x2 y3 t = appendl x0 y1 (appendl x2 y3 t)

-- It's possible and maybe desirable to give a more efficient implementation
appendr2 : HairyFingers x y -> x -> y -> x -> y -> HairyFingers x y
appendr2 t x0 y1 x2 y3 = appendr (appendr t x0 y1) x2 y3

-- It's possible and maybe desirable to give a more efficient implementation
appendl3 : x -> y -> x -> y -> x -> y -> HairyFingers x y -> HairyFingers x y
appendl3 x0 y1 x2 y3 x4 y5 t = appendl x0 y1 (appendl x2 y3 (appendl x4 y5 t))

-- It's possible and maybe desirable to give a more efficient implementation
appendr3 : HairyFingers x y -> x -> y -> x -> y -> x -> y -> HairyFingers x y
appendr3 t x0 y1 x2 y3 x4 y5 = appendr (appendr (appendr t x0 y1) x2 y3) x4 y5


concat2 : HairyFingers x y -> x -> y -> x -> y -> HairyFingers x y -> HairyFingers x y
concat2 t1 x0 y1 x2 y3 Empty = appendr2 t1 x0 y1 x2 y3
concat2 Empty x0 y1 x2 y3 t2 = appendl2 x0 y1 x2 y3 t2
concat2 (Singleton x0 y1) x2 y3 x4 y5 t2 = appendl3 x0 y1 x2 y3 x4 y5 t2
concat2 t1 x0 y1 x2 y3 (Singleton x4 y5) = appendr3 t1 x0 y1 x2 y3 x4 y5
concat2 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 x4 y5 (Deep (Digit1 x6 y7) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2
concat2 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 x4 y5 (Deep (Digit2 x6 y7 x8 y9) m2 r2) = Deep l1 (concat2 m1 x0 (Node3 y1 x2 y3 x4 y5) x6 (Node2 y7 x8 y9) m2) r2
concat2 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 x6 y7 (Deep (Digit1 x8 y9) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node3 y5 x6 y7 x8 y9) m2) r2
concat2 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 x6 y7 (Deep (Digit2 x8 y9 xa yb) m2 r2) = Deep l1 (concat2 m1 x0 (Node3 y1 x2 y3 x4 y5) x6 (Node3 y7 x8 y9 xa yb) m2) r2

concat1 : HairyFingers x y -> x -> y -> HairyFingers x y -> HairyFingers x y
concat1 t1 x1 y2 Empty = appendr t1 x1 y2
concat1 Empty x1 y2 t2 = appendl x1 y2 t2
concat1 (Singleton x0 y1) x2 y3 t2 = appendl2 x0 y1 x2 y3 t2
concat1 t1 x0 y1 (Singleton x2 y3) = appendr2 t1 x0 y1 x2 y3
concat1 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 (Deep (Digit1 x4 y5) m2 r2) = Deep l1 (concat1 m1 x0 (Node2 y1 x2 y3) m2) r2
concat1 (Deep l1 m1 (Digit1 x0 y1)) x2 y3 (Deep (Digit2 x4 y5 x6 y7) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat1 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 (Deep (Digit1 x6 y7) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat1 (Deep l1 m1 (Digit2 x0 y1 x2 y3)) x4 y5 (Deep (Digit2 x6 y7 x8 y9) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2

concat : HairyFingers x y -> HairyFingers x y -> HairyFingers x y
concat t1 Empty = t1
concat Empty t2 = t2
concat (Singleton x0 y1) (Singleton x2 y3) = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)
concat (Singleton x0 y1) t2 = appendl x0 y1 t2
concat t1 (Singleton x1 y0) = appendr t1 x1 y0
concat (Deep l1 m1 (Digit1 x0 y1)) (Deep (Digit1 x2 y3) m2 r2) = Deep l1 (concat1 m1 x0 (Node2 y1 x2 y3) m2) r2
concat (Deep l1 m1 (Digit1 x0 y1)) (Deep (Digit2 x2 y3 x4 y5) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat (Deep l1 m1 (Digit2 x0 y1 x2 y3)) (Deep (Digit1 x4 y5) m2 r2) = Deep l1 (concat1 m1 x0 (Node3 y1 x2 y3 x4 y5) m2) r2
concat (Deep l1 m1 (Digit2 x0 y1 x2 y3)) (Deep (Digit2 x4 y5 x6 y7) m2 r2) = Deep l1 (concat2 m1 x0 (Node2 y1 x2 y3) x4 (Node2 y5 x6 y7) m2) r2


maybeSingleton : Maybe (x, y) -> HairyFingers x y
maybeSingleton Nothing = Empty
maybeSingleton (Just (x,y)) = Singleton x y


digitToTree : Digit x y -> HairyFingers x y
digitToTree (Digit1 x0 y1) = Singleton x0 y1
digitToTree (Digit2 x0 y1 x2 y3) = Deep (Digit1 x0 y1) Empty (Digit1 x2 y3)


alterl : (Functor f) => (x -> y -> f (Maybe (x, y))) -> HairyFingers x y -> Maybe (f (HairyFingers x y))
alterl _ Empty = Nothing
alterl f (Singleton x0 y1) = Just (maybeSingleton <$> f x0 y1)
alterl f (Deep (Digit1 x0 y1) m r) = let
  h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
  h x0 (Node2 y1 x2 y3) = (Digit2 x0 y1 x2 y3, Nothing)
  h x0 (Node3 y1 x2 y3 x4 y5) = (Digit1 x0 y1, Just (x2, Node2 y3 x4 y5))
  g : Maybe (x, y) -> HairyFingers x y
  g (Just (x0', y1')) = Deep (Digit1 x0' y1') m r
  g Nothing = case alterl h m of
    Nothing => digitToTree r
    Just (l, m') => Deep l m' r
  in Just (g <$> f x0 y1)
alterl f (Deep (Digit2 x0 y1 x2 y3) m r) = let
  g : Maybe (x, y) -> Digit x y
  g Nothing = Digit1 x2 y3
  g (Just (x0', y1')) = Digit2 x0' y1' x2 y3
  h : Digit x y -> HairyFingers x y
  h l' = Deep l' m r
  in Just (h . g <$> f x0 y1)

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


alterr : (Functor f) => (x -> y -> f (Maybe (x, y))) -> HairyFingers x y -> Maybe (f (HairyFingers x y))
alterr _ Empty = Nothing
alterr f (Singleton x0 y1) = Just (maybeSingleton <$> f x0 y1)
alterr f (Deep l m (Digit1 x0 y1)) = let
  h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
  h x0 (Node2 y1 x2 y3) = (Digit2 x0 y1 x2 y3, Nothing)
  h x0 (Node3 y1 x2 y3 x4 y5) = (Digit1 x4 y5, Just (x0, Node2 y1 x2 y3))
  g : Maybe (x, y) -> HairyFingers x y
  g (Just (x0', y1')) = Deep l m (Digit1 x0' y1')
  g Nothing = case alterr h m of
    Nothing => digitToTree l
    Just (r, m') => Deep l m r
  in Just (g <$> f x0 y1)
alterr f (Deep l m (Digit2 x0 y1 x2 y3)) = let
  g : Maybe (x, y) -> Digit x y
  g Nothing = Digit1 x0 y1
  g (Just (x2', y3')) = Digit2 x0 y1 x2' y3'
  in Just (Deep l m . g <$> f x2 y3)

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


||| Either returns an element found, or an indication of whether it's
||| less than any element, greater than any element, or within
lookup : (x -> Ordering) -> (y -> Either Ordering x) -> HairyFingers x y -> Either Ordering x
lookup o p Empty = Nothing
lookup o p (Singleton x y) = case o x of
  LT => Nothing
  EQ => Just x
  GT => p y
lookup o p (Deep l m r) = ?d

{-
||| This implementation packs nodes fairly tightly: given a long list
||| most nodes will be node3.
fromList : (Monoid v, Measured x v, Measured y v) => [(x,y)] -> HairyFingers x y
fromList = let

  inner : (x,y) -> [(x,y)] -> (Digit x y, [Node x y])
  inner (x1,y2) [] = (digit1 x1 y2, [])
  inner (x1,y2) [(x3,y4)] = (digit2 x1 y2 x3 y4, [])
  inner (x1,y2) [(x3,y4),(x5,y6)] = (digit1 x1 y2, [node2 x3 y4 x5 y6])
  inner (x1,y2) ((x3,y4):(x5,y6):p:l) = (node3 x1 y2 x3 y4 x5 y6 :) <$> inner p l

  go : [(x,y)] -> HairyFingers x y
  go [] = Empty
  go [(x1,y2)] = singleton x1 y2
  go ((x1,y2)::p::t) = let
    (r,m) = inner p t
    in deep (digit1 x1 y2) (fromList m) r

  in go


-}
