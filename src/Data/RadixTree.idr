module Data.RadixTree

import Data.Map
import Data.String


-- commonInitial "cucumber" "cupcake"  ~~>  ("cu", "cumber", "pcake")
commonInitial : String -> String -> (String, String, String)



record RadixTree a where
  constructor MkRadix
  content : Maybe a
  children : Map Char (String, RadixTree a)

empty : RadixTree a
empty = MkRadix Nothing empty

singletonEmpty : a -> RadixTree a
singletonEmpty x = MkRadix (Just x) empty

singleton : String -> a -> RadixTree a
singleton s x = case strM s of
  StrNil => singletonEmpty x
  StrCons h _ => MkRadix Nothing $ singleton h (s, singletonEmpty x)

-- Quite sensibly, the code can't see that "insert" makes progress
insert : String -> a -> RadixTree a -> RadixTree a
insert r x (MkRadix c m) = case strM r of
  StrNil => MkRadix (Just x) m
  StrCons h _ => MkRadix c $ alter h (Just . plonk r) m where
    plonk : String -> Maybe (String, RadixTree a) -> (String, RadixTree a)
    plonk s Nothing = (s, singletonEmpty x)
    plonk s (Just (t, p@(MkRadix d n))) = assert_total $ let
      (u, s', t') = commonInitial s t
      in MkPair u $ case (strM s', strM t') of
        (StrNil, StrNil) => MkRadix (Just x) n
        (StrNil, StrCons j _) => MkRadix (Just x) $ singleton j (t', p)
        (StrCons i _, StrNil) => MkRadix d $ alter i (Just . plonk s') n
        (StrCons i _, StrCons j _) => MkRadix Nothing $ fromList [(i, (s', singletonEmpty x)), (j, (t', p))]

commonPrefix : RadixTree a -> Maybe (String, RadixTree a)
commonPrefix (MkRadix (Just _) _) = Nothing
commonPrefix (MkRadix Nothing m) = case singletonView m of
  Nothing => Nothing
  Just (c,t) => Just t
