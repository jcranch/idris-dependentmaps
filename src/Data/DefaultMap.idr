||| Maps with a default element
module Data.DefaultMap

import Data.Filterable

import Data.Map


public export
record DefMap (k : Type) {v : Type} (d : v) where
  constructor MkDef
  nodef : Map k v

export
length : DefMap k d -> Nat
length = length . nodef

export
empty : DefMap k d
empty = MkDef empty

export
alldefault : DefMap k d -> Bool
alldefault = Data.Map.null . nodef

nondefault : Eq v => v -> v -> Maybe v
nondefault x y = if x == y then Nothing else Just y

export
map' : (Ord k, Eq v) => {x : u} -> (f : u -> v) -> DefMap k x -> DefMap k (f x)
map' f (MkDef m) = MkDef $ mapMaybe (nondefault (f x) . f) m

export
lookup : Ord k => {x : v} -> k -> DefMap k x -> v
lookup a (MkDef m) = case lookup a m of
  Nothing => x
  Just y => y

export
lookupIn : Ord k => {x : v} -> DefMap k x -> k -> v
lookupIn m a = lookup a m

