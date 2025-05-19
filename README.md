# Dependent Maps in Idris

Here's an implementation of dependent maps in Idris 2 (with a type of
keys `k : Type`, and a type of values `v : k -> Type` dependent upon
it); it's an alternative to the
[https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Data/SortedMap/Dependent.idr](version)
already in `contrib`.

It uses size-balanced binary trees of the sort suggested by Chen: each
node cannot be smaller than either of its sibling's children.

Some of the functions (in particular, `lookup`) require an `DecEq`
instance for the keys (as well as the more familiar instance of
`Ord`). This seems unavoidable: if such a map has a key `x : k` and a
value `y : v x`, then looking up `x'` will require a proof that `x =
x'` to return a `v x'`.

A few unit tests are provided (I look forward to a more convenient
framework for unit testing in Idris).

## Things to do

### Verify balance algorithms

We have the `Balanced` type, which expresses Chen's notion of
balancedness; it would be good to go through the algorithms and check
that they behave correctly in the sense that they preserved
`Balanced`ness.
