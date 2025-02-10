module Test.StringMap

import Data.StringMap


tests : List (Lazy Bool)
tests = [
  commonPrefix "" "" == ("", "", ""),
  commonPrefix "" "cat" == ("", "", "cat"),
  commonPrefix "cat" "" == ("", "cat", ""),
  commonPrefix "cat" "cat" == ("cat", "", ""),
  commonPrefix "category" "cat" == ("cat", "egory", ""),
  commonPrefix "cat" "category" == ("cat", "", "egory"),
  commonPrefix "category" "cataclysm" == ("cat", "egory", "aclysm")
  ]

export
testStringMap : IO ()
testStringMap = do
  putStrLn "StringMap:"
  putStrLn $ if and tests then "  All tests passed!" else "  Some failures."
