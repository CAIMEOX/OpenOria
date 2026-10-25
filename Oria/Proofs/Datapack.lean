module

import Oria
import Oria.Datapack
import Oria.Proofs.Fixtures.Datapack
meta import Oria
meta import Oria.Datapack
meta import Oria.Proofs.Fixtures.Datapack

namespace Oria.Proofs.Datapack

open Oria Oria.Std Oria.Datapack

@[mcfunction]
def home : Prog (Grade.handled (Teleport.grade .self
    (.world (.absolute (.static 0)) (.absolute (.static 80)) (.absolute (.static 0))))) Unit :=
  (Teleport.to .self
    (.world (.absolute (.static 0)) (.absolute (.static 80))
      (.absolute (.static 0)))).ignore

@[mcfunction]
def ready : Prog (Grade.handled .pure) Unit := Prog.pure Val.unit

def aliases : Datapack.Builder Unit := do
  for path in [PublicFunctionPath.ofString "home", .ofString "debug/home.v1"] do
    entry path home.ref

@[datapack]
def demo : Datapack.Spec :=
  Datapack.build { ns := .ofString "demo", description := "Oria teleport demo" } do
    aliases
    entry (.ofString "imported") Fixtures.Datapack.run.ref
    onLoad ready.ref
    onLoad ready.ref
    onTick ready.ref

private def contents (path : String) : Option String :=
  demo.artifact.files.findSome? fun file =>
    if file.path.toString == path then some file.contents else none

#guard contents "data/demo/function/home.mcfunction" ==
  contents "data/demo/function/debug/home.v1.mcfunction"
#guard (contents "data/demo/function/home.mcfunction").isSome
#guard (contents "data/minecraft/tags/function/load.json").isSome
#guard (contents "data/minecraft/tags/function/tick.json").isSome
#guard (contents "pack.mcmeta").isSome
#guard Fixtures.Datapack.imported.artifact.files.any fun file =>
  file.path.toString == "data/imported/function/run.mcfunction"
#guard !(Fixtures.Datapack.imported.artifact.files.any fun file =>
  file.path.toString == "data/minecraft/tags/function/tick.json")

@[datapack]
def emptyPack : Spec := build { ns := .ofString "empty" } (pure ())

#guard emptyPack.artifact.files.size == 3

end Oria.Proofs.Datapack
