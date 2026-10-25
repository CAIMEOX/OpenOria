module

import Oria.Data.IndexedVector
meta import Oria.Data.IndexedVector
import Oria.IR.Common.Signature
import Std.Tactic

namespace Oria.Proofs.IndexedVector

open Oria.Data

private def ExampleFamily : Fin 2 → Type :=
  Fin.cases Nat (fun _ : Fin 1 => String)

private def buildExample (position : Fin 2) : Except String (ExampleFamily position) :=
  Fin.cases (.ok (42 : Nat)) (fun _ : Fin 1 => .ok "forty-two") position

private def exampleValues : Except String (IndexedVector ExampleFamily) :=
  IndexedVector.ofFnM buildExample

private def zero : Fin 2 := ⟨0, by decide⟩
private def one : Fin 2 := ⟨1, by decide⟩

private theorem familyZero : ExampleFamily zero = Nat := by rfl
private theorem familyOne : ExampleFamily one = String := by rfl

private def getZero (values : IndexedVector ExampleFamily) : Nat :=
  familyZero ▸ values.get zero

private def getOne (values : IndexedVector ExampleFamily) : String :=
  familyOne ▸ values.get one

private def zeroResult : Nat :=
  match exampleValues with
  | .error _ => 0
  | .ok values => getZero values

private def oneResult : String :=
  match exampleValues with
  | .error _ => "error"
  | .ok values => getOne values

#guard zeroResult == 42
#guard oneResult == "forty-two"


end Oria.Proofs.IndexedVector
