module

import Oria.Compiler.Optimize.Machine
import Oria.IR.Machine.Pretty
meta import Oria.Compiler.Optimize.Machine
meta import Oria.IR.Machine.Pretty

namespace Oria.Proofs.MachineOptimize

open Oria Oria.IR.Machine

private def permutation : Def [] ⟨2, 2⟩ := {
  layout := [2, 2, 2]
  entry := IR.Scope.Var.head
  blocks := Data.IndexedVector.ofFn fun
    | ⟨0, _⟩ => by
        change Body [] [2, 2, 2] 2 2
        exact .done (.jump ⟨IR.Scope.Var.head.weaken 2, #v[.var 1, .var 0]⟩)
    | ⟨1, _⟩ => by
        change Body [] [2, 2, 2] 2 2
        exact .done (.jump ⟨(IR.Scope.Var.head.weaken 2).weaken 2, #v[.var 0, .var 1]⟩)
    | ⟨2, _⟩ => by
        change Body [] [2, 2, 2] 2 2
        exact .done (.ret #v[.var 0, .var 1]) }

private def returns (d : Def [] ⟨2, 2⟩) : Option (Vector (Atom 2) 2) :=
  match d.block d.entry with
  | .done (.ret values) => some values
  | _ => none

theorem forwarded_arguments :
    ((Optimize.Machine.controlFlow `permutation permutation).toOption.bind returns) =
      some #v[.var 1, .var 0] := by native_decide

/-- One call followed by arithmetic, across a block-parameter binding. -/
private def sequential : Def [⟨0, 1⟩] ⟨0, 1⟩ := {
  layout := [0, 1, 0]
  entry := IR.Scope.Var.head
  blocks := Data.IndexedVector.ofFn fun
    | ⟨0, _⟩ => .step (.call IR.Scope.Var.head #v[])
        (.done (.jump ⟨IR.Scope.Var.head.weaken 0, #v[.var 0]⟩))
    | ⟨1, _⟩ => by
        change Body [⟨0, 1⟩] [0, 1, 0] 1 1
        exact .step (.binary .add (.var 0) (.lit 7)) (.done (.ret #v[.var 0]))
    | ⟨2, _⟩ => .done (.ret #v[.lit 99]) }

private def sequentialShape (d : Def [⟨0, 1⟩] ⟨0, 1⟩) : Bool :=
  d.layout == [0] && match d.block d.entry with
  | .step (.call _ _) (.step (.binary .add (.var i) (.lit 7)) (.done (.ret values))) =>
      i.val == 0 && values == #v[.var 0]
  | _ => false

theorem call_order :
    (Optimize.Machine.controlFlow `sequential sequential).toOption.any sequentialShape := by
  native_decide

/-- Distinct branch arguments retain a shared successor even when its body is effectful. -/
private def shared : Def [⟨1, 1⟩] ⟨1, 1⟩ := {
  layout := [1, 1]
  entry := IR.Scope.Var.head
  blocks := Data.IndexedVector.ofFn fun
    | ⟨0, _⟩ => by
        change Body [⟨1, 1⟩] [1, 1] 1 1
        exact .done (.branch (.isTrue (.var 0))
          ⟨IR.Scope.Var.head.weaken 1, #v[.lit 10]⟩
          ⟨IR.Scope.Var.head.weaken 1, #v[.lit 20]⟩)
    | ⟨1, _⟩ => by
        change Body [⟨1, 1⟩] [1, 1] 1 1
        exact .step (.call IR.Scope.Var.head #v[.var 0]) (.done (.ret #v[.var 0])) }

theorem shared_successor :
    (Optimize.Machine.controlFlow `shared shared).toOption.map (·.layout) = some [1, 1] := by
  native_decide

private def loop : Def [] ⟨2, 0⟩ := {
  layout := [2, 2]
  entry := IR.Scope.Var.head
  blocks := Data.IndexedVector.ofFn fun
    | ⟨0, _⟩ => by
        change Body [] [2, 2] 0 2
        exact .done (.jump ⟨IR.Scope.Var.head.weaken 2, #v[.var 1, .var 0]⟩)
    | ⟨1, _⟩ => by
        change Body [] [2, 2] 0 2
        exact .done (.jump ⟨IR.Scope.Var.head, #v[.var 0, .var 1]⟩) }

private def loopShape (d : Def [] ⟨2, 0⟩) : Bool :=
  d.layout == [2] && match d.block d.entry with
  | .done (.jump e) =>
      if h : e.arity = 2 then e.target.index == d.entry.index &&
        (h ▸ e.values) == #v[.var 1, .var 0]
      else false
  | _ => false

theorem loop_backedge : (Optimize.Machine.controlFlow `loop loop).toOption.any loopShape := by
  native_decide

private def chosen (value : Int32) : Def [] ⟨0, 1⟩ := {
  layout := [0, 0, 0]
  entry := IR.Scope.Var.head
  blocks := Data.IndexedVector.ofFn fun
    | ⟨0, _⟩ => .done (.switch (.lit value)
        [(3, ⟨IR.Scope.Var.head.weaken 0, #v[]⟩)]
        (some ⟨(IR.Scope.Var.head.weaken 0).weaken 0, #v[]⟩))
    | ⟨1, _⟩ => .done (.ret #v[.lit 30])
    | ⟨2, _⟩ => .done (.ret #v[.lit 40]) }

private def literalResult (d : Def [] ⟨0, 1⟩) : Option Int32 :=
  match d.block d.entry with
  | .done (.ret values) => match values[0] with
      | .lit n => some n
      | _ => none
  | _ => none

theorem switch_choice :
    ((Optimize.Machine.controlFlow `chosen (chosen 3)).toOption.bind literalResult) = some 30 := by
  native_decide

theorem switch_fallback :
    ((Optimize.Machine.controlFlow `chosen (chosen 7)).toOption.bind literalResult) = some 40 := by
  native_decide

private def through (tag : Int32) : Def [] ⟨1, 1⟩ := {
  layout := [1, 2, 1, 0]
  entry := IR.Scope.Var.head
  blocks := Data.IndexedVector.ofFn fun
    | ⟨0, _⟩ => by
        change Body [] [1, 2, 1, 0] 1 1
        exact .done (.jump ⟨IR.Scope.Var.head.weaken 1, #v[.lit tag, .var 0]⟩)
    | ⟨1, _⟩ => by
        change Body [] [1, 2, 1, 0] 1 2
        exact .done (.switch (.var 0)
          [(1, ⟨(IR.Scope.Var.head.weaken 2).weaken 1, #v[.var 1]⟩)]
          (some ⟨((IR.Scope.Var.head.weaken 1).weaken 2).weaken 1, #v[]⟩))
    | ⟨2, _⟩ => by
        change Body [] [1, 2, 1, 0] 1 1
        exact .done (.ret #v[.var 0])
    | ⟨3, _⟩ => .done (.ret #v[.lit (-1)]) }

private def returnsArgument (d : Def [] ⟨1, 1⟩) : Bool :=
  d.layout == [1] && match d.block d.entry with
    | .done (.ret vs) => vs == #v[.var 0]
    | _ => false

theorem threaded_payload :
    (Optimize.Machine.controlFlow `through (through 1)).toOption.any returnsArgument := by
  native_decide

end Oria.Proofs.MachineOptimize
