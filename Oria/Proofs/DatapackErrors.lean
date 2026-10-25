module

import Oria
import Oria.Datapack
import Oria.Proofs.Fixtures.Datapack
meta import Oria
meta import Oria.Datapack
meta import Oria.Proofs.Fixtures.Datapack

namespace Oria.Proofs.DatapackErrors

open Oria Oria.Std Oria.Datapack

@[mcfunction]
def unitArgument (_ : Val Unit) : Prog (Grade.handled .pure) Unit := Prog.pure Val.unit

@[mcfunction]
def number : Prog .pure Int32 := Prog.pure 1

@[mcfunction]
def optional : Prog .pure (Option Unit) := Oria.Option.none

@[mcfunction]
def move : Prog (Grade.handled ⟨9#8, 67#16⟩) Unit :=
  (Teleport.to .self
    (.world (.absolute (.static 0)) (.absolute (.static 80))
      (.absolute (.static 0)))).ignore

def collision.artifact : Nat := 0

/--
error: generated datapack declaration
-/
#guard_msgs(error, substring := true) in
@[datapack]
def collision : Spec := build { ns := .ofString "test" } (pure ())

/--
error: datapack
-/
#guard_msgs(error, substring := true) in
@[datapack]
def duplicate : Spec := build { ns := .ofString "test" } do
  entry (.ofString "run") Fixtures.Datapack.run.ref
  entry (.ofString "run") Fixtures.Datapack.run.ref

/--
error: datapack
-/
#guard_msgs(error, substring := true) in
@[datapack]
def absent : Spec := build { ns := .ofString "test" } do
  entry (.ofString "run") (IR.DeclRef.named (sig := ⟨[], .unit, .pure⟩) `absent)

/--
error: datapack
-/
#guard_msgs(error, substring := true) in
@[datapack]
def missingCommand : Spec := build { ns := .ofString "test", commands := some [] } do
  entry (.ofString "move") move.ref

end Oria.Proofs.DatapackErrors
