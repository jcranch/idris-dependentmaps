module Data.Misc

import Decidable.Equality

-- Should probably be in a standard library!
public export
subst : {0 v : k -> Type} -> x = y -> v x -> v y
subst Refl u = u

export
[eqDPairFromDec] {0 v : k -> Type} -> (DecEq k, {x : k} -> Eq (v x)) => Eq (DPair k v) where
  MkDPair k1 v1 == MkDPair k2 v2 = case decEq k1 k2 of
    Yes p => subst {v = v} p v1 == v2
    No _ => False

-- Should perhaps go in decidable equality
export
fromDPair : DecEq k => {0 v : k -> Type} -> (x : k) -> DPair k v -> Maybe (v x)
fromDPair x (MkDPair y a) = case decEq y x of
    Yes p => Just (subst {v = v} p a)
    No _  => Nothing

