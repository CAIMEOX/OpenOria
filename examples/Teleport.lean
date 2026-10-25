module

import Oria
import Oria.Datapack
meta import Oria
meta import Oria.Datapack

open Oria Oria.Std Oria.Datapack

@[mcfunction]
def home : Prog (Teleport.grade .self
    (.world (.absolute (.static 0)) (.absolute (.static 80)) (.absolute (.static 0)))) Unit :=
  (Teleport.to .self
    (.world (.absolute (.static 0)) (.absolute (.static 80))
      (.absolute (.static 0)))).ignore

@[datapack]
def demo : Spec :=
  build { ns := "demo", description := "Oria teleport demo" } do
    entry "home" home.ref

public def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (.userError "usage: lake exe oria-teleport <empty-directory>")
  demo.artifact.writeTo destination
