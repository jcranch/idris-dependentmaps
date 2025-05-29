module Data.DependentMap

import Data.HairyFingerTree


export
data DMap : (k : Type) -> (k -> Type) -> Type where
  MkDMap : Maybe (Hairy (DPair k v) ()) -> DMap k v


