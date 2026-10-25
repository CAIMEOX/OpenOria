module

import Oria.Compiler.RegAlloc.LinearScan
public meta import Oria.Compiler.RegAlloc.LinearScan

namespace Oria.Proofs.RegisterAllocation

open Oria.RegAlloc

private def firstRegister
    (assignment : Assignment 2 #[some ⟨0, 1⟩]) : Option Nat :=
  match assignment.homes.get ⟨0, by decide⟩ with
  | some (.reg register) => some register.val
  | _ => none

private def slotsOf
    {registers : Nat} {ranges : Array (Option Range)} :
    Option (Assignment registers ranges) → Option Nat
  | none => none
  | some assignment => some assignment.slots

private def firstTwoStackHomes
    (assignment : Assignment 0 #[some ⟨0, 1⟩, some ⟨1, 2⟩]) : Option (Nat × Nat) :=
  match assignment.homes.get ⟨0, by decide⟩, assignment.homes.get ⟨1, by decide⟩ with
  | some (.stack left), some (.stack right) => some (left.val, right.val)
  | _, _ => none

example : (allocate 0 #[]).isSome = true := by native_decide

example :
    (allocate 1 #[some ⟨0, 5⟩, some ⟨1, 2⟩]).any (fun assignment =>
      match assignment.homes[0], assignment.homes[1] with
      | some (.stack _), some (.reg _) => true
      | _, _ => false) = true := by native_decide

example : (allocate 0 #[some ⟨0, 2⟩, some ⟨1, 4⟩]).isSome = true := by
  native_decide

example :
    slotsOf (allocate 0 #[some ⟨0, 1⟩, some ⟨1, 2⟩, some ⟨2, 3⟩]) = some 1 := by
  native_decide

example :
    (allocate 0 #[some ⟨0, 1⟩, some ⟨1, 2⟩]).map firstTwoStackHomes = some (some (0, 0)) := by
  native_decide

example :
    slotsOf (allocate 1 #[some ⟨0, 10⟩, some ⟨1, 3⟩, some ⟨2, 4⟩]) = some 2 := by
  native_decide

example :
    slotsOf (allocate 2 #[some ⟨0, 10⟩, some ⟨1, 3⟩, some ⟨2, 4⟩]) = some 1 := by
  native_decide

example :
    slotsOf (allocate 1 #[some ⟨0, 5⟩, some ⟨1, 2⟩, some ⟨2, 6⟩]) = some 1 := by
  native_decide

example :
    slotsOf (allocate 1 #[some ⟨0, 5⟩, some ⟨0, 2⟩, some ⟨0, 3⟩]) = some 2 := by
  native_decide

example :
    slotsOf (allocate 1 #[none, some ⟨0, 3⟩, none, some ⟨3, 4⟩]) = some 0 := by
  native_decide

example : (allocate 1 #[some ⟨3, 3⟩]).isSome = false := by
  native_decide

example : (allocate 1 #[some ⟨3, 1⟩]).isSome = false := by
  native_decide

example :
    (allocate 2 #[some ⟨0, 1⟩]
      (fun _ register => if register.val == 0 then 10 else 0)).map firstRegister = some (some 1) := by
  native_decide

end Oria.Proofs.RegisterAllocation
