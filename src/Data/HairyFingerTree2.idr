module Data.HairyFingerTree2


data LeftEnd : (x : Type) -> (y : Type) -> Type where
  Left1 : y -> x -> LeftEnd x y
  Left2 : y -> x -> y -> x -> LeftEnd x y

data RightEnd : (x : Type) -> (y : Type) -> Type where
  Right2 : x -> y -> x -> y -> RightEnd x y
  Right3 : x -> y -> x -> y -> x -> y -> RightEnd x y

data Node : (x : Type) -> (y : Type) -> Type where
  Node2 : y -> x -> y -> Node x y
  Node3 : y -> x -> y -> x -> y -> Node x y

data Hairy : (x : Type) -> (y : Type) -> Type where
  Zero : y -> Hairy x y
  One : y -> x -> y -> Hairy x y
  Two : y -> x -> y -> x -> y -> Hairy x y
  Three : y -> x -> y -> x -> y -> x -> y -> Hairy x y
  Lots : LeftEnd x y -> Hairy x (Node x y) -> RightEnd x y -> Hairy x y

four : y -> x -> y -> x -> y -> x -> y -> x -> y -> Hairy x y
four y0 x1 y2 x3 y4 x5 y6 x7 y8 = Lots (Left1 y0 x1) (Zero (Node2 y2 x3 y4)) (Right2 x5 y6 x7 y8)

five : y -> x -> y -> x -> y -> x -> y -> x -> y -> x -> y -> Hairy x y
five y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya = Lots (Left1 y0 x1) (Zero (Node3 y2 x3 y4 x5 y6)) (Right2 x7 y8 x9 ya)

six : y -> x -> y -> x -> y -> x -> y -> x -> y -> x -> y -> x -> y -> Hairy x y
six y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya xb yc = Lots (Left1 y0 x1) (One (Node2 y2 x3 y4) x5 (Node2 y6 x7 y8)) (Right2 x9 ya xb yc)


appendl : y -> x -> Hairy x y -> Hairy x y
appendl y0 x1 (Zero y2) = One y0 x1 y2
appendl y0 x1 (One y2 x3 y4) = Two y0 x1 y2 x3 y4
appendl y0 x1 (Two y2 x3 y4 x5 y6) = Three y0 x1 y2 x3 y4 x5 y6
appendl y0 x1 (Three y2 x3 y4 x5 y6 x7 y8) = four y0 x1 y2 x3 y4 x5 y6 x7 y8
appendl y0 x1 (Lots (Left1 y2 x3) m r) = Lots (Left2 y0 x1 y2 x3) m r
appendl y0 x1 (Lots (Left2 y2 x3 y4 x5) m r) = Lots (Left1 y0 x1) (appendl (Node2 y2 x3 y4) x5 m) r

appendl2 : y -> x -> y -> x -> Hairy x y -> Hairy x y
appendl2 y0 x1 y2 x3 (Zero y4) = Two y0 x1 y2 x3 y4
appendl2 y0 x1 y2 x3 (One y4 x5 y6) = Three y0 x1 y2 x3 y4 x5 y6
appendl2 y0 x1 y2 x3 (Two y4 x5 y6 x7 y8) = four y0 x1 y2 x3 y4 x5 y6 x7 y8
appendl2 y0 x1 y2 x3 (Three y4 x5 y6 x7 y8 x9 ya) = five y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya
appendl2 y0 x1 y2 x3 (Lots (Left1 y4 x5) m r) = Lots (Left1 y0 x1) (appendl (Node2 y2 x3 y4) x5 m) r
appendl2 y0 x1 y2 x3 (Lots (Left2 y4 x5 y6 x7) m r) = Lots (Left1 y0 x1) (appendl (Node3 y2 x3 y4 x5 y6) x7 m) r

appendl3 : y -> x -> y -> x -> y -> x -> Hairy x y -> Hairy x y
appendl3 y0 x1 y2 x3 y4 x5 (Zero y6) = Three y0 x1 y2 x3 y4 x5 y6
appendl3 y0 x1 y2 x3 y4 x5 (One y6 x7 y8) = four y0 x1 y2 x3 y4 x5 y6 x7 y8
appendl3 y0 x1 y2 x3 y4 x5 (Two y6 x7 y8 x9 ya) = five y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya
appendl3 y0 x1 y2 x3 y4 x5 (Three y6 x7 y8 x9 ya xb yc) = six y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya xb yc
appendl3 y0 x1 y2 x3 y4 x5 (Lots (Left1 y6 x7) m r) = Lots (Left1 y0 x1) (appendl (Node3 y2 x3 y4 x5 y6) x7 m) r
appendl3 y0 x1 y2 x3 y4 x5 (Lots (Left2 y6 x7 y8 x9) m r) = Lots (Left2 y0 x1 y2 x3) (appendl (Node3 y4 x5 y6 x7 y8) x9 m) r

appendl4 : y -> x -> y -> x -> y -> x -> y -> x -> Hairy x y -> Hairy x y
appendl4 y0 x1 y2 x3 y4 x5 y6 x7 m = appendl2 y0 x1 y2 x3 (appendl2 y4 x5 y6 x7 m)

appendr : Hairy x y -> x -> y -> Hairy x y
appendr (Zero y0) x1 y2 = One y0 x1 y2
appendr (One y0 x1 y2) x3 y4 = Two y0 x1 y2 x3 y4
appendr (Two y0 x1 y2 x3 y4) x5 y6 = Three y0 x1 y2 x3 y4 x5 y6
appendr (Three y0 x1 y2 x3 y4 x5 y6) x7 y8 = four y0 x1 y2 x3 y4 x5 y6 x7 y8
appendr (Lots l m (Right2 x0 y1 x2 y3)) x4 y5 = Lots l m (Right3 x0 y1 x2 y3 x4 y5)
appendr (Lots l m (Right3 x0 y1 x2 y3 x4 y5)) x6 y7 = Lots l (appendr m x0 (Node2 y1 x2 y3)) (Right2 x4 y5 x6 y7)

appendr2 : Hairy x y -> x -> y -> x -> y -> Hairy x y
appendr2 (Zero y0) x1 y2 x3 y4 = Two y0 x1 y2 x3 y4
appendr2 (One y0 x1 y2) x3 y4 x5 y6 = Three y0 x1 y2 x3 y4 x5 y6
appendr2 (Two y0 x1 y2 x3 y4) x5 y6 x7 y8 = four y0 x1 y2 x3 y4 x5 y6 x7 y8
appendr2 (Three y0 x1 y2 x3 y4 x5 y6) x7 y8 x9 ya = five y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya
appendr2 (Lots l m (Right2 x0 y1 x2 y3)) x4 y5 x6 y7 = Lots l (appendr m x0 (Node2 y1 x2 y3)) (Right2 x4 y5 x6 y7)
appendr2 (Lots l m (Right3 x0 y1 x2 y3 x4 y5)) x6 y7 x8 y9 = Lots l (appendr m x0 (Node3 y1 x2 y3 x4 y5)) (Right2 x6 y7 x8 y9)

appendr3 : Hairy x y -> x -> y -> x -> y -> x -> y -> Hairy x y
appendr3 (Zero y0) x1 y2 x3 y4 x5 y6 = Three y0 x1 y2 x3 y4 x5 y6
appendr3 (One y0 x1 y2) x3 y4 x5 y6 x7 y8 = four y0 x1 y2 x3 y4 x5 y6 x7 y8
appendr3 (Two y0 x1 y2 x3 y4) x5 y6 x7 y8 x9 ya = five y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya
appendr3 (Three y0 x1 y2 x3 y4 x5 y6) x7 y8 x9 ya xb yc = six y0 x1 y2 x3 y4 x5 y6 x7 y8 x9 ya xb yc
appendr3 (Lots l m (Right2 x0 y1 x2 y3)) x4 y5 x6 y7 x8 y9 = Lots l (appendr m x0 (Node3 y1 x2 y3 x4 y5)) (Right2 x6 y7 x8 y9)
appendr3 (Lots l m (Right3 x0 y1 x2 y3 x4 y5)) x6 y7 x8 y9 xa yb = Lots l (appendr m x0 (Node3 y1 x2 y3 x4 y5)) (Right3 x6 y7 x8 y9 xa yb)

appendr4 : Hairy x y -> x -> y -> x -> y -> x -> y -> x -> y -> Hairy x y
appendr4 m x0 y1 x2 y3 x4 y5 x6 y7 = appendr2 (appendr2 m x0 y1 x2 y3) x4 y5 x6 y7

appendLeftEnd : LeftEnd x y -> Hairy x y -> Hairy x y
appendLeftEnd (Left1 y0 x1) t = appendl y0 x1 t
appendLeftEnd (Left2 y0 x1 y2 x3) t = appendl2 y0 x1 y2 x3 t

appendRightEnd : Hairy x y -> RightEnd x y -> Hairy x y
appendRightEnd t (Right2 x0 y1 x2 y3) = appendr2 t x0 y1 x2 y3
appendRightEnd t (Right3 x0 y1 x2 y3 x4 y5) = appendr3 t x0 y1 x2 y3 x4 y5


empty : Hairy x ()
empty = Zero ()


concat1 : Hairy x y -> x -> Hairy x y -> Hairy x y
concat1 (Zero y0) x1 v = appendl y0 x1 v
concat1 (One y0 x1 y2) x3 v = appendl2 y0 x1 y2 x3 v
concat1 (Two y0 x1 y2 x3 y4) x5 v = appendl3 y0 x1 y2 x3 y4 x5 v
concat1 (Three y0 x1 y2 x3 y4 x5 y6) x7 v = appendl4 y0 x1 y2 x3 y4 x5 y6 x7 v
concat1 u x0 (Zero y1) = appendr u x0 y1
concat1 u x0 (One y1 x2 y3) = appendr2 u x0 y1 x2 y3
concat1 u x0 (Two y1 x2 y3 x4 y5) = appendr3 u x0 y1 x2 y3 x4 y5
concat1 u x0 (Three y1 x2 y3 x4 y5 x6 y7) = appendr4 u x0 y1 x2 y3 x4 y5 x6 y7
concat1 (Lots l1 m1 (Right2 x0 y1 x2 y3)) x4 (Lots (Left1 y5 x6) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node3 y1 x2 y3 x4 y5)) x6 m2) r2
concat1 (Lots l1 m1 (Right2 x0 y1 x2 y3)) x4 (Lots (Left2 y5 x6 y7 x8) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node2 y1 x2 y3)) x4 (appendl (Node2 y5 x6 y7) x8 m2)) r2
concat1 (Lots l1 m1 (Right3 x0 y1 x2 y3 x4 y5)) x6 (Lots (Left1 y7 x8) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node2 y1 x2 y3)) x4 (appendl (Node2 y5 x6 y7) x8 m2)) r2
concat1 (Lots l1 m1 (Right3 x0 y1 x2 y3 x4 y5)) x6 (Lots (Left2 y7 x8 y9 xa) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node2 y1 x2 y3)) x4 (appendl (Node3 y5 x6 y7 x8 y9) xa m2)) r2

concat : Hairy x () -> Hairy x () -> Hairy x ()
concat u (Zero _) = u
concat (Zero _) v = v
concat (One _ x0 _) v = appendl () x0 v
concat u (One _ x0 _) = appendr u x0 ()
concat (Two _ x0 _ x1 _) v = appendl2 () x0 () x1 v
concat u (Two _ x0 _ x1 _) = appendr2 u x0 () x1 ()
concat (Three _ x0 _ x1 _ x2 _) v = appendl3 () x0 () x1 () x2 v
concat u (Three _ x0 _ x1 _ x2 _) = appendr3 u x0 () x1 () x2 ()
concat (Lots l1 m1 (Right2 x0 _ x1 _)) (Lots (Left1 _ x2) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node2 () x1 ())) x2 m2) r2
concat (Lots l1 m1 (Right2 x0 _ x1 _)) (Lots (Left2 _ x2 _ x3) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node3 () x1 () x2 ())) x3 m2) r2
concat (Lots l1 m1 (Right3 x0 _ x1 _ x2 _)) (Lots (Left1 _ x3) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node3 () x1 () x2 ())) x3 m2) r2
concat (Lots l1 m1 (Right3 x0 _ x1 _ x2 _)) (Lots (Left2 _ x3 _ x4) m2 r2) = Lots l1 (concat1 (appendr m1 x0 (Node2 () x1 ())) x2 (appendl (Node2 () x3 ()) x4 m2)) r2


alterl : Functor f => (y -> x -> f (Maybe (y, x))) -> Hairy x y -> Either y (f (Hairy x y))
alterl _ (Zero y0) = Left y0
alterl p (One y0 x1 y2) = let
  q : Maybe (y, x) -> Hairy x y
  q Nothing = Zero y2
  q (Just (y0', x1')) = One y0' x1' y2
  in Right (q <$> p y0 x1)
alterl p (Two y0 x1 y2 x3 y4) = let
  q : Maybe (y, x) -> Hairy x y
  q Nothing = One y2 x3 y4
  q (Just (y0', x1')) = Two y0' x1' y2 x3 y4
  in Right (q <$> p y0 x1)
alterl p (Three y0 x1 y2 x3 y4 x5 y6) = let
  q : Maybe (y, x) -> Hairy x y
  q Nothing = Two y2 x3 y4 x5 y6
  q (Just (y0', x1')) = Three y0' x1' y2 x3 y4 x5 y6
  in Right (q <$> p y0 x1)
alterl p (Lots (Left1 y0 x1) m r) = let
  s : Node x y -> x -> (LeftEnd x y, Maybe (Node x y, x))
  s (Node2 y2 x3 y4) x5 = (Left2 y2 x3 y4 x5, Nothing)
  s (Node3 y2 x3 y4 x5 y6) x7 = (Left1 y2 x3, Just (Node2 y4 x5 y6, x7))
  q : Maybe (y, x) -> Hairy x y
  q Nothing = case alterl s m of
    Left n => case (n, r) of
      (Node2 y2 x3 y4, Right2 x5 y6 x7 y8) => Three y2 x3 y4 x5 y6 x7 y8
      (Node2 y2 x3 y4, Right3 x5 y6 x7 y8 x9 ya) => four y2 x3 y4 x5 y6 x7 y8 x9 ya
      (Node3 y2 x3 y4 x5 y6, Right2 x7 y8 x9 ya) => four y2 x3 y4 x5 y6 x7 y8 x9 ya
      (Node3 y2 x3 y4 x5 y6, Right3 x7 y8 x9 ya xb yc) => five y2 x3 y4 x5 y6 x7 y8 x9 ya xb yc
    Right (l', m') => Lots l' m' r
  q (Just (y0', x1')) = Lots (Left1 y0' x1') m r
  in Right (q <$> p y0 x1)
alterl p (Lots (Left2 y0 x1 y2 x3) m r) = let
  q : Maybe (y, x) -> Hairy x y
  q Nothing = Lots (Left1 y2 x3) m r
  q (Just (y0', x1')) = Lots (Left2 y0 x1 y2 x3) m r
  in Right (q <$> p y0 x1)

alterr : Functor f => (x -> y -> f (Maybe (x, y))) -> Hairy x y -> Either y (f (Hairy x y))
alterr _ (Zero y0) = Left y0
alterr p (One y0 x1 y2) = let
  q : Maybe (x, y) -> Hairy x y
  q Nothing = Zero y0
  q (Just (x1', y2')) = One y0 x1' y2'
  in Right (q <$> p x1 y2)
alterr p (Two y0 x1 y2 x3 y4) = let
  q : Maybe (x, y) -> Hairy x y
  q Nothing = One y0 x1 y2
  q (Just (x3', y4')) = Two y0 x1 y2 x3' y4'
  in Right (q <$> p x3 y4)
alterr p (Three y0 x1 y2 x3 y4 x5 y6) = let
  q : Maybe (x, y) -> Hairy x y
  q Nothing = Two y0 x1 y2 x3 y4
  q (Just (x5', y6')) = Three y0 x1 y2 x3 y4 x5' y6'
  in Right (q <$> p x5 y6)
alterr p (Lots l m (Right2 x0 y1 x2 y3)) = let
  s : x -> Node x y -> (RightEnd x y, Maybe (x, Node x y))
  s a0 (Node2 b1 a2 b3) = (Right2 a0 b1 a2 b3, Nothing)
  s a0 (Node3 b1 a2 b3 a4 b5) = (Right3 a0 b1 a2 b3 a4 b5, Nothing)
  q : Maybe (x, y) -> Hairy x y
  q Nothing = case alterr s m of
    Left n => case (l, n) of
      (Left1 b0 a1, Node2 b2 a3 b4) => Two b0 a1 b2 a3 b4
      (Left1 b0 a1, Node3 b2 a3 b4 a5 b6) => Three b0 a1 b2 a3 b4 a5 b6
      (Left2 b0 a1 b2 a3, Node2 b4 a5 b6) => Three b0 a1 b2 a3 b4 a5 b6
      (Left2 b0 a1 b2 a3, Node3 b4 a5 b6 a7 b8) => four b0 a1 b2 a3 b4 a5 b6 a7 b8
    Right (r', m') => Lots l m' r'
  q (Just (x2', y3')) = Lots l m (Right2 x0 y1 x2' y3')
  in Right (q <$> p x2 y3)
alterr p (Lots l m (Right3 x0 y1 x2 y3 x4 y5)) = let
  q : Maybe (x, y) -> Hairy x y
  q Nothing = Lots l m (Right2 x0 y1 x2 y3)
  q (Just (x4', y5')) = Lots l m (Right3 x0 y1 x2 y3 x4' y5')
  in Right (q <$> p x4 y5)

viewl : Hairy x y -> (y, Maybe (x, Hairy x y))
viewl m = let
  q : y -> x -> ((y, x), Maybe (y, x))
  q y0 x1 = ((y0, x1), Nothing)
  in case alterl q m of
    Left y0 => (y0, Nothing)
    Right ((y0, x1), m') => (y0, Just (x1, m'))

viewr : Hairy x y -> (Maybe (Hairy x y, x), y)
viewr m = let
  q : x -> y -> ((x, y), Maybe (x, y))
  q x0 y1 = ((x0, y1), Nothing)
  in case alterr q m of
    Left y1 => (Nothing, y1)
    Right ((x0, y1), m') => (Just (m', x0), y1)


nodeToTree : Node x y -> Hairy x y
nodeToTree (Node2 y0 x1 y2) = One y0 x1 y2
nodeToTree (Node3 y0 x1 y2 x3 y4) = Two y0 x1 y2 x3 y4


splitL : ((x -> Ordering) -> y -> (Hairy x y, Maybe x, Hairy x y))
      -> (x -> Ordering) -> LeftEnd x y -> Maybe (Hairy x y, Maybe x, Hairy x y -> Hairy x y)
splitL h p (Left1 y0 x1) = case p x1 of
  LT => let
    (l, m, r) = h p y0
    in Just (l, m, concat1 r x1)
  EQ => Just (Zero y0, Just x1, id)
  GT => Nothing
splitL h p (Left2 y0 x1 y2 x3) = case p x3 of
  LT => case p x1 of
    LT => let
      (l, m, r) = h p y0
      in Just (l, m, concat1 r x1 . appendl y2 x3)
    EQ => Just (Zero y0, Just x1, appendl y2 x3)
    GT => let
      (l, m, r) = h p y2
      in Just (appendl y0 x1 l, m, concat1 r x3)
  EQ => Just (One y0 x1 y2, Just x3, id)
  GT => Nothing

splitR : ((x -> Ordering) -> y -> (Hairy x y, Maybe x, Hairy x y))
      -> (x -> Ordering) -> RightEnd x y -> Maybe (Hairy x y -> Hairy x y, Maybe x, Hairy x y)
splitR h p (Right2 x0 y1 x2 y3) = case p x0 of
  LT => Nothing
  EQ => Just (id, Just x0, One y1 x2 y3)
  GT => case p x2 of
    LT => let
      (l, m, r) = h p y1
      in Just (\z => concat1 z x0 l, m, appendr r x2 y3)
    EQ => Just (\z => appendr z x0 y1, Just x2, Zero y3)
    GT => let
      (l, m, r) = h p y3
      in Just (\z => concat1 (appendr z x0 y1) x2 l, m, r)
splitR h p (Right3 x0 y1 x2 y3 x4 y5) = case p x0 of
  LT => Nothing
  EQ => Just (id, Just x0, Two y1 x2 y3 x4 y5)
  GT => case p x4 of
    LT => case p x2 of
      LT => let
        (l, m, r) = h p y1
        in Just (\z => concat1 z x0 l, m, appendr2 r x2 y3 x4 y5)
      EQ => Just (\z => appendr z x0 y1, Just x2, One y3 x4 y5)
      GT => let
        (l, m, r) = h p y3
        in Just (\z => concat1 (appendr z x0 y1) x2 l, m, appendr r x4 y5)
    EQ => Just (\z => appendr2 z x0 y1 x2 y3, Just x4, Zero y5)
    GT => let
      (l, m, r) = h p y5
      in Just (\z => concat1 (appendr2 z x0 y1 x2 y3) x4 l, m, r)


splitNode : ((x -> Ordering) -> y -> (Hairy x y, Maybe x, Hairy x y))
         -> (x -> Ordering) -> Node x y -> (Hairy x y, Maybe x, Hairy x y)
splitNode h p (Node2 y0 x1 y2) = case p x1 of
  LT => let
    (l, m, r) = h p y0
    in (l, m, appendr r x1 y2)
  EQ => (Zero y0, Just x1, Zero y2)
  GT => let
    (l, m, r) = h p y2
    in (appendl y0 x1 l, m, r)
splitNode h p (Node3 y0 x1 y2 x3 y4) = case p x1 of
  LT => let
    (l, m, r) = h p y0
    in (l, m, appendr2 r x1 y2 x3 y4)
  EQ => (Zero y0, Just x1, One y2 x3 y4)
  GT => case p x3 of
    LT => let
      (l, m, r) = h p y2
      in (appendl y0 x1 l, m, appendr r x3 y4)
    EQ => (One y0 x1 y2, Just x3, Zero y4)
    GT => let
      (l, m, r) = h p y4
      in (appendl2 y0 x1 y2 x3 l, m, r)

split : ((x -> Ordering) -> y -> (Hairy x y, Maybe x, Hairy x y))
     -> (x -> Ordering) -> Hairy x y -> (Hairy x y, Maybe x, Hairy x y)
split h p (Zero y0) = h p y0
split h p (One y0 x1 y2) = case p x1 of
  LT => let
    (l, m, r) = h p y0
    in (l, m, appendr r x1 y2)
  EQ => (Zero y0, Just x1, Zero y2)
  GT => let
    (l, m, r) = h p y2
    in (appendl y0 x1 l, m, r)
split h p (Two y0 x1 y2 x3 y4) = case p x1 of
  LT => let
    (l, m, r) = h p y0
    in (l, m, appendr2 r x1 y2 x3 y4)
  EQ => (Zero y0, Just x1, One y2 x3 y4)
  GT => case p x3 of
    LT => let
      (l, m, r) = h p y2
      in (appendl y0 x1 l, m, appendr r x3 y4)
    EQ => (One y0 x1 y2, Just x3, Zero y4)
    GT => let
      (l, m, r) = h p y4
      in (appendl2 y0 x1 y2 x3 l, m, r)
split h p (Three y0 x1 y2 x3 y4 x5 y6) = case p x3 of
  LT => case p x1 of
    LT => let
      (l, m, r) = h p y0
      in (l, m, appendr3 r x1 y2 x3 y4 x5 y6)
    EQ => (Zero y0, Just x1, Two y2 x3 y4 x5 y6)
    GT => let
      (l, m, r) = h p y2
      in (appendl y0 x1 l, m, appendr2 r x3 y4 x5 y6)
  EQ => (One y0 x1 y2, Just x3, One y4 x5 y6)
  GT => case p x5 of
    LT => let
      (l, m, r) = h p y4
      in (appendl2 y0 x1 y2 x3 l, m, appendr r x5 y6)
    EQ => (Two y0 x1 y2 x3 y4, Just x5, Zero y6)
    GT => let
      (l, m, r) = h p y6
      in (appendl3 y0 x1 y2 x3 y4 x5 l, m, r)
split h p (Lots l m r) = case splitL h p l of
  Just (l', u, g) => ?z
  Nothing => case splitR h p r of
    Just (f, u, r') => ?y
    Nothing => let
      (l'', u, r'') = split (splitNode h) p m
      in ?wtf

