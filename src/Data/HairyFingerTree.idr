module Data.HairyFingerTree


interface Monoid v => Measured x v where
  measure : x -> v


data Node : Type -> Type -> Type -> Type where
  Node2 : v -> y -> x -> y -> Node v x y
  Node3 : v -> y -> x -> y -> x -> y -> Node v x y

Monoid v => Measured (Node v x y) v where
  measure (Node2 a _ _ _) = a
  measure (Node3 a _ _ _ _ _) = a

node2 : (Monoid v, Measured x v, Measured y v) => y -> x -> y -> Node v x y
node2 y0 x1 y2 = Node2 (measure y0 <+> measure x1 <+> measure y2) y0 x1 y2

node3 : (Monoid v, Measured x v, Measured y v) => y -> x -> y -> x -> y -> Node v x y
node3 y0 x1 y2 x3 y4 = Node3 (measure y0 <+> measure x1 <+> measure y2 <+> measure x3 <+> measure y4) y0 x1 y2 x3 y4


data Digit : Type -> Type -> Type -> Type where
  Digit1 : v -> x -> y -> Digit v x y
  Digit2 : v -> x -> y -> x -> y -> Digit v x y

Monoid v => Measured (Digit v x y) v where
  measure (Digit1 a _ _) = a
  measure (Digit2 a _ _ _ _) = a

digit1 : (Monoid v, Measured x v, Measured y v) => x -> y -> Digit v x y
digit1 x1 y2 = Digit1 (measure x1 <+> measure y2) x1 y2

digit2 : (Monoid v, Measured x v, Measured y v) => x -> y -> x -> y -> Digit v x y
digit2 x1 y2 x3 y4 = Digit2 (measure x1 <+> measure y2 <+> measure x3 <+> measure y4) x1 y2 x3 y4


data HairyFingers : Type -> Type -> Type -> Type where
  Empty : HairyFingers v x y
  Singleton : v -> x -> y -> HairyFingers v x y
  Deep : v -> Digit v x y -> HairyFingers v x (Node v x y) -> Digit v x y -> HairyFingers v x y

Monoid v => Measured (HairyFingers v x y) v where
  measure Empty = neutral
  measure (Singleton a _ _) = a
  measure (Deep a _ _ _) = a

singleton : (Monoid v, Measured x v, Measured y v) => x -> y -> HairyFingers v x y
singleton x0 y1 = Singleton (measure x0 <+> measure y1) x0 y1

appendl : (Monoid v, Measured x v, Measured y v) => v -> x -> y -> HairyFingers v x y -> HairyFingers v x y
appendl a01 x0 y1 Empty = Singleton a01 x0 y1
appendl a01 x0 y1 (Singleton a23 x2 y3) = Deep (a01 <+> a23) (Digit1 a01 x0 y1) Empty (Digit1 a23 x2 y3)
appendl a01 x0 y1 (Deep a2n (Digit1 a23 x2 y3) m r) = Deep (a01 <+> a2n) (Digit2 (a01 <+> a23) x0 y1 x2 y3) m r
appendl a01 x0 y1 (Deep a2n (Digit2 a25 x2 y3 x4 y5) m r) = Deep (a01 <+> a2n) (Digit1 a01 x0 y1) (appendl a25 x2 (node2 y3 x4 y5) m) r

appendr : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> v -> x -> y -> HairyFingers v x y
appendr Empty a10 x1 y0 = Singleton a10 x1 y0
appendr (Singleton a32 x3 y2) a10 x1 y0 = Deep (a32 <+> a10) (Digit1 a32 x3 y2) Empty (Digit1 a10 x1 y0)
appendr (Deep an2 l m (Digit1 a32 x3 y2)) a10 x1 y0 = Deep (an2 <+> a10) l m (Digit2 (a32 <+> a10) x3 y2 x1 y0)
appendr (Deep an2 l m (Digit2 a52 x5 y4 x3 y2)) a10 x1 y0 = Deep (an2 <+> a10) l (appendr m a52 x5 (node2 y4 x3 y2)) (Digit1 a10 x1 y0)

appendl2 : (Monoid v, Measured x v, Measured y v) => v -> x -> y -> v -> x -> y -> HairyFingers v x y -> HairyFingers v x y
appendl2 = ?al2

appendr2 : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> v -> x -> y -> v -> x -> y -> HairyFingers v x y
appendr2 = ?ar2

appendl3 : (Monoid v, Measured x v, Measured y v) => v -> x -> y -> v -> x -> y -> v -> x -> y -> HairyFingers v x y -> HairyFingers v x y
appendl3 = ?al3

appendr3 : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> v -> x -> y -> v -> x -> y -> v -> x -> y -> HairyFingers v x y
appendr3 = ?ar3

mutual
  concat : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> HairyFingers v x y -> HairyFingers v x y
  concat t1 Empty = t1
  concat Empty t2 = t2
  concat (Singleton a01 x0 y1) (Singleton a23 x2 y3) = Deep (a01 <+> a23) (Digit1 a01 x0 y1) Empty (Digit1 a23 x2 y3)
  concat (Singleton a01 x0 y1) d@(Deep _ _ _ _) = appendl a01 x0 y1 d
  concat d@(Deep _ _ _ _) (Singleton a10 x1 y0) = appendr d a10 x1 y0
  concat (Deep a l1 m1 (Digit1 b x1 y2)) (Deep a' (Digit1 b' x3 y4) m2 r2) = ?w_5
  concat (Deep a l1 m1 (Digit1 b x1 y2)) (Deep a' (Digit2 b' x3 y4 x5 y6) m2 r2) = ?w_6
  concat (Deep a l1 m1 (Digit2 b x1 y2 x3 y4)) (Deep a' (Digit1 b' x5 y6) m2 r2) = ?w_7
  concat (Deep a l1 m1 (Digit2 b x1 y2 x3 y4)) (Deep a' (Digit2 b' x5 y6 x7 y8) m2 r2) = ?w_8

  concat1 : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> v -> x -> y -> HairyFingers v x y -> HairyFingers v x y
  concat1 t1 a12 x1 y2 Empty = appendr t1 a12 x1 y2
  concat1 Empty a12 x1 y2 t2 = appendl a12 x1 y2 t2
  concat1 (Singleton a01 x0 y1) a23 x2 y3 t2 = ?v1
  concat1 t1 a01 x0 y1 (Singleton a23 x2 y3) = ?v2
  concat1 (Deep a l1 m1 (Digit1 b x1 y2)) a34 x3 y4 (Deep a' (Digit1 b' x5 y6) m2 r2) = ?v_5
  concat1 (Deep a l1 m1 (Digit1 b x1 y2)) a34 x3 y4 (Deep a' (Digit2 b' x5 y6 x7 y8) m2 r2) = ?v_6
  concat1 (Deep a l1 m1 (Digit2 b x1 y2 x3 y4)) a56 x5 y6 (Deep a' (Digit1 b' x7 y8) m2 r2) = ?v_7
  concat1 (Deep a l1 m1 (Digit2 b x1 y2 x3 y4)) a56 x5 y6 (Deep a' (Digit2 b' x7 y8 x9 y10) m2 r2) = ?v_8

  concat2 : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> x -> y -> x -> y -> HairyFingers v x y -> HairyFingers v x y
  concat2 = ?w2

maybeSingleton : Maybe (x, y) -> HairyFingers v x y
maybeSingleton = ?ms

alterl : (Monoid v, Measured x v, Measured y v, Functor f) => (x -> y -> f (Maybe (x, y))) -> HairyFingers v x y -> Maybe (f (HairyFingers v x y))
alterl _ Empty = Nothing
alterl f (Singleton _ x0 y1) = Just (maybeSingleton <$> f x0 y1)
alterl f (Deep _ (Digit1 a01 x0 y1) m r) = ?at1
alterl f (Deep _ (Digit2 a03 x0 y1 x2 y3) m r) = ?at2

alterr : (Monoid v, Measured x v, Measured y v, Functor f) => ((x, y) -> f (Maybe (x, y))) -> HairyFingers v x y -> Maybe (f (HairyFingers v x y))
alterr = ?ar

viewl : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> Maybe (v, x, y, HairyFingers v x y)
viewl Empty = Nothing
viewl (Singleton a x1 y2) = Just (a, x1, y2, Empty)
viewl (Deep a (Digit1 a12 x1 y2) m r) = ?vl_3
viewl (Deep a (Digit2 a14 x1 y2 x3 y4) m r) = ?vl_4

viewr : (Monoid v, Measured x v, Measured y v) => HairyFingers v x y -> Maybe (HairyFingers v x y, v, x, y)
viewr Empty = Nothing
viewr (Singleton a x1 y2) = Just (Empty, a, x1, y2)
viewr (Deep a l m r) = ?vr_2


||| This implementation packs nodes fairly tightly: given a long list
||| most nodes will be node3.
fromList : (Monoid v, Measured x v, Measured y v) => [(x,y)] -> HairyFingers v x y
fromList = let

  inner : (x,y) -> [(x,y)] -> (Digit x y, [Node x y])
  inner (x1,y2) [] = (digit1 x1 y2, [])
  inner (x1,y2) [(x3,y4)] = (digit2 x1 y2 x3 y4, [])
  inner (x1,y2) [(x3,y4),(x5,y6)] = (digit1 x1 y2, [node2 x3 y4 x5 y6])
  inner (x1,y2) ((x3,y4):(x5,y6):p:l) = (node3 x1 y2 x3 y4 x5 y6 :) <$> inner p l

  go : [(x,y)] -> HairyFingers v x y
  go [] = Empty
  go [(x1,y2)] = singleton x1 y2
  go ((x1,y2)::p::t) = let
    (r,m) = inner p t
    in deep (digit1 x1 y2) (fromList m) r

  in go
