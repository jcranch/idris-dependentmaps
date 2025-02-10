module Main
import Control.App
import Control.App.Spec
import StringMapSpec
import DependentMapSpec

main : IO ()
main = do run (new emptyState (do
  StringMapSpec.spec
  DependentMapSpec.spec

  specFinalReport))
