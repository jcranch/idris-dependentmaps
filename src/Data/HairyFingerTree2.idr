module Data.HairyFingerTree2


data Node : Type -> Type -> Type where
  Node2 : (y0 : y) -> (x1 : x) -> (y2 : y) -> Node x y
  Node3 : (y0 : y) -> (x1 : x) -> (y2 : y) -> (x3 : x) -> (y4 : y) -> Node x y

-- Could have longer digits; I think the concatenation algorithm would
-- get only a little more annoying to write
data LeftEnd : (x : Type) -> (y : Type) -> Type where
  Left1 : (x0 : x) -> (y1 : y) -> LeftEnd x y
  Left2 : (x0 : x) -> (y1 : y) -> (x2 : x) -> (y3 : y) -> LeftEnd x y

data RightEnd : (x : Type) -> (y : Type) -> Type where
  Right1 : (y0 : y) -> (x1 : x) -> RightEnd x y
  Right2 : (y0 : y) -> (x1 : x) -> (y2 : y) -> (x3 : x) -> RightEnd x y

data Hairy : (x : Type) -> (y : Type) -> Type where
  One : (x0 : x) -> Hairy x y
  Two : (x0 : x) -> (y1 : y) -> (x2 : x) -> Hairy x y
  Lots : (l : LeftEnd x y) -> (m : Hairy x (Node x y)) -> (r : RightEnd x y) -> Hairy x y


appendl : x -> y -> Hairy x y -> Hairy x y
appendl x0 y1 (One x2) = Two x0 y1 x2
appendl x0 y1 (Two x2 y3 x4) = Lots (Left1 x0 y1) (One x2) (Right1 y3 x4)
appendl x0 y1 (Lots (Left1 x2 y3) m r) = Lots (Left2 x0 y1 x2 y3) m r
appendl x0 y1 (Lots (Left2 x2 y3 x4 y5) m r) = Lots (Left1 x0 y1) (appendl x2 (Node2 y3 x4 y5) m) r

appendl2 : x -> y -> x -> y -> Hairy x y -> Hairy x y
appendl2 x0 y1 x2 y3 (One x4) = Lots (Left1 x0 y1) (One x2) (Right1 y3 x4)
appendl2 x0 y1 x2 y3 (Two x4 y5 x6) = Lots (Left2 x0 y1 x2 y3) (One x4) (Right1 y5 x6)
appendl2 x0 y1 x2 y3 (Lots (Left1 x4 y5) m r) = Lots (Left1 x0 y1) (appendl x2 (Node2 y3 x4 y5) m) r
appendl2 x0 y1 x2 y3 (Lots (Left2 x4 y5 x6 y7) m r) = Lots (Left2 x0 y1 x2 y3) (appendl x4 (Node2 y5 x6 y7) m) r

appendr : Hairy x y -> y -> x -> Hairy x y
appendr (One x0) y1 x2 = Two x0 y1 x2
appendr (Two x0 y1 x2) y3 x4 = Lots (Left1 x0 y1) (One x2) (Right1 y3 x4)
appendr (Lots l m (Right1 y0 x1)) y2 x3 = Lots l m (Right2 y0 x1 y2 x3)
appendr (Lots l m (Right2 y0 x1 y2 x3)) y4 x5 = Lots l (appendr m (Node2 y0 x1 y2) x3) (Right1 y4 x5)

appendr2 : Hairy x y -> y -> x -> y -> x -> Hairy x y
appendr2 (One x0) y1 x2 y3 x4 = Lots (Left1 x0 y1) (One x2) (Right1 y3 x4)
appendr2 (Two x0 y1 x2) y3 x4 y5 x6 = Lots (Left1 x0 y1) (One x2) (Right2 y3 x4 y5 x6)
appendr2 (Lots l m (Right1 y0 x1)) y2 x3 y4 x5 = Lots l (appendr m (Node2 y0 x1 y2) x3) (Right1 y4 x5)
appendr2 (Lots l m (Right2 y0 x1 y2 x3)) y4 x5 y6 x7 = Lots l (appendr m (Node2 y0 x1 y2) x3) (Right2 y4 x5 y6 x7)

concat : Hairy x y -> y -> Hairy x y -> Hairy x y
concat (One x0) y1 v = appendl x0 y1 v
concat u y0 (One x1) = appendr u y0 x1
concat (Two x0 y1 x2) y3 v = appendl2 x0 y1 x2 y3 v
concat u y0 (Two x1 y2 x3) = appendr2 u y0 x1 y2 x3
concat (Lots l m (Right1 y0 x1)) y2 (Lots (Left1 x3 y4) m' r') = Lots l (concat m (Node3 y0 x1 y2 x3 y4) m') r'
concat (Lots l m (Right1 y0 x1)) y2 (Lots (Left2 x3 y4 x5 y6) m' r') = Lots l (concat m (Node2 y0 x1 y2) $ appendl x3 (Node2 y4 x5 y6) m') r'
concat (Lots l m (Right2 y0 x1 y2 x3)) y4 (Lots (Left1 x5 y6) m' r') = Lots l (concat m (Node2 y0 x1 y2) $ appendl x3 (Node2 y4 x5 y6) m') r'
concat (Lots l m (Right2 y0 x1 y2 x3)) y4 (Lots (Left2 x5 y6 x7 y8) m' r') = Lots l (concat m (Node2 y0 x1 y2) $ appendl x3 (Node3 y4 x5 y6 x7 y8) m') r'


foldLeft : Monoid m => (x -> m) -> (y -> m) -> LeftEnd x y -> m
foldLeft f g (Left1 x0 y1) = f x0 <+> g y1
foldLeft f g (Left2 x0 y1 x2 y3) = f x0 <+> g y1 <+> f x2 <+> g y3

foldRight : Monoid m => (x -> m) -> (y -> m) -> RightEnd x y -> m
foldRight f g (Right1 y0 x1) = g y0 <+> f x1
foldRight f g (Right2 y0 x1 y2 x3) = g y0 <+> f x1 <+> g y2 <+> f x3

foldNode : Monoid m => (x -> m) -> (y -> m) -> Node x y -> m
foldNode f g (Node2 y0 x1 y2) = g y0 <+> f x1 <+> g y2
foldNode f g (Node3 y0 x1 y2 x3 y4) = g y0 <+> f x1 <+> g y2 <+> f x3 <+> g y4

foldMap : Monoid m => (x -> m) -> (y -> m) -> Hairy x y -> m
foldMap f _ (One x0) = f x0
foldMap f g (Two x0 y1 x2) = f x0 <+> g y1 <+> f x2
foldMap f g (Lots l m r) = foldLeft f g l <+> foldMap f (foldNode f g) m <+> foldRight f g r


Bifunctor LeftEnd where
  bimap f g (Left1 x0 y1) = Left1 (f x0) (g y1)
  bimap f g (Left2 x0 y1 x2 y3) = Left2 (f x0) (g y1) (f x2) (g y3)

Bifunctor RightEnd where
  bimap f g (Right1 y0 x1) = Right1 (g y0) (f x1)
  bimap f g (Right2 y0 x1 y2 x3) = Right2 (g y0) (f x1) (g y2) (f x3)

Bifunctor Node where
  bimap f g (Node2 y0 x1 y2) = Node2 (g y0) (f x1) (g y2)
  bimap f g (Node3 y0 x1 y2 x3 y4) = Node3 (g y0) (f x1) (g y2) (f x3) (g y4)

Bifunctor Hairy where
  bimap f g (One x0) = One (f x0)
  bimap f g (Two x0 y1 x2) = Two (f x0) (g y1) (f x2)
  bimap f g (Lots l m r) = Lots (bimap f g l) (bimap f (bimap f g) m) (bimap f g r)


alterl : Functor f => (x -> f x) -> Hairy x y -> f (Hairy x y)
alterl g (One x0) = One <$> g x0
alterl g (Two x0 y1 x2) = (\z => Two z y1 x2) <$> g x0
alterl g (Lots (Left1 x0 y1) m r) = (\z => Lots (Left1 z y1) m r) <$> g x0
alterl g (Lots (Left2 x0 y1 x2 y3) m r) = (\z => Lots (Left2 z y1 x2 y3) m r) <$> g x0


{-
alterl' : Functor f
       => (x -> f x)
       -> (x -> y -> f (Maybe (x, y)))
       -> Hairy x y
       -> f (Hairy x y)
alterl' p _ (One x0) = One <$> p x0
alterl' _ q (Two x0 y1 x2) = let
  h : Maybe (x, y) -> Hairy x y
  h (Just (x0', y1')) = Two x0' y1' x2
  h Nothing = One x2
  in h <$> q x0 y1
alterl' p q (Lots (Left1 x0 y1) m r) = let
  h : Maybe (x, y) -> Hairy x y
  h (Just (x0', y1')) = Lots (Left1 x0' y1') m r
  h Nothing = let
    s : x -> Node x y -> (Either x . Pair (LeftEnd x y)) (Maybe (x, Node x y))
    s x2 (Node3 y3 x4 y5 x6 y7) = (Right (Left1 x2 y3, Just (x4, Node2 y5 x6 y7)))
    s x2 (Node2 y3 x4 y5) = (Right (Left2 x2 y3 x4 y5, Nothing))
    in case alterl' Left s m of
      Left x2 => case r of
        Right1 y3 x4 => Two x2 y3 x4
        Right2 y3 x4 y5 x6 => Lots (Left1 x2 y3) (One x4) (Right1 y5 x6)
      Right (l', m') => Lots l' m' r
  in h <$> q x0 y1
alterl' _ q (Lots (Left2 x0 y1 x2 y3) m r) = let
  h : Maybe (x, y) -> Hairy x y
  h (Just (x0', y1')) = Lots (Left2 x0' y1' x2 y3) m r
  h Nothing = Lots (Left1 x2 y3) m r
  in h <$> q x0 y1
-}


{-
mutual
  lotsMR : (m : Hairy x (Node x y)) -> (r : RightEnd x y) -> Hairy x y
  lotsMR = let
    h : x -> Node x y -> (Digit x y, Maybe (x, Node x y))
    h x0 (Node2 y1 x2 y3) = (Left2 x0 y1 x2 y3, Nothing)
    h x0 (Node3 y1 x2 y3 x4 y5) = (Left1 x0 y1, Just (x2, Node2 y3 x4 y5))
    in case alterl' h m of

  viewl : Hairy x y -> (x, Maybe (y, Hairy x y))
  viewl (One x0) = (x0, Nothing)
  viewl (Two x0 y1 x2) = (x0, Just (y1, One x2))
  viewl (Lots (Left1 x0 y1) m r) with (viewl m)
    viewl (Lots (Left1 x0 y1) m r) | with_pat = ?u_3_rhs
  viewl (Lots (Left2 x0 y1 x2 y3) m r) = (x0, Just (y1, Lots (Left1 x2 y3) m r))

  alterl' : Functor f => (x -> y -> f (Maybe (x, y))) -> Hairy x y -> Maybe (f (Hairy x y))
  alterl' _ (One x0) = Nothing
  alterl' g (Two x0 y1 x2) = let
    h : Maybe (x, y) -> Hairy x y
    h Nothing = One x2
    h (Just (x0', y1')) = Two x0' y1' x2
    in Just (h <$> g x0 y1)
  alterl' g (Lots (Left1 x0 y1) m r) = ?t_3
  alterl' g (Lots (Left2 x0 y1 x2 y3) m r) = let
    h : Maybe (x, y) -> Hairy x y
    h Nothing = Lots (Left1 x2 y3) m r
    h (Just (x0', y1')) = Lots (Left2 x0' y1' x2 y3) m r
    in Just (h <$> g x0 y1)
-}


{-
-- alterr


-- lensLeft : 
-}
