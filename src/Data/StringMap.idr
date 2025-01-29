module Data.StringMap

import Data.Filterable
import Data.Map
import Data.String


||| It's possible there could be faster ways of doing this
export
commonPrefix : String -> String -> (String, String, String)
commonPrefix u v = let
  r : Int = cast (length u)
  s : Int = cast (length v)
  m : Int = min r s
  go : Int -> (String, String, String)
  go i = assert_total $ if i == m || (strIndex u i /= strIndex v i)
    then (substr 0 (cast i) u, substr (cast i) (cast (r-i)) u, substr (cast i) (cast (s-i)) v)
    else go (i+1)
  in go 0

export
record StringMap v where
  constructor MkStringMap
  content : Maybe v
  children : Map Char (String, StringMap v)

export
empty : StringMap v
empty = MkStringMap Nothing empty

export
null : StringMap v -> Bool
null (MkStringMap (Just _) _) = False
null (MkStringMap Nothing m) = Data.Map.null m

export
singleton : String -> v -> StringMap v
singleton s x = case strM s of
  StrNil => MkStringMap (Just x) empty
  StrCons h _ => MkStringMap Nothing $ singleton h (s,MkStringMap (Just x) empty)

export
lookup : String -> StringMap v -> Maybe v
lookup s = let
  l = cast (length s)
  go : Int -> StringMap v -> Maybe v
  go i (MkStringMap c m) = assert_total $ case compare i l of
    LT => case lookup (strIndex s i) m of
      Just (t,n) => if isPrefixOf t s
        then go (i + cast (length t)) n
        else Nothing
      Nothing => Nothing
    EQ => c
    GT => Nothing -- Shouldn't happen
  in go 0

insert :: String -> v -> StringMap v -> Maybe v
insert s v = let
  l = cast (length s)
  go : Int -> StringMap v -> StringMap v
  
  in go 0

export
Functor StringMap where
  map f (MkStringMap a m) = MkStringMap (map f a) (map (map (map f)) m)

||| If all strings stored have a common prefix, emit it
export
hasCommonPrefix : StringMap v -> Maybe (String, StringMap v)
hasCommonPrefix (MkStringMap (Just _) _) = Nothing
hasCommonPrefix (MkStringMap Nothing m) = snd <$> singletonView m
