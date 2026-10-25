module

import Oria.Compiler.Optimize.Sharing
import Oria.IR.DP121.Transform
meta import Oria.Compiler.Optimize.Sharing

namespace Oria.Proofs.Sharing

open Oria Oria.Datapack Oria.Target.DP121

private def ref {k : FunctionKind} (path : ResourcePath) : FunctionRef k :=
  .ofId (.ofParts "sharing" path)

private def leaf (path : ResourcePath) : (k : FunctionKind) × FunctionDef k :=
  ⟨.plain, ⟨ref path, .plain #[.returnValue 0]⟩⟩

private def call (path target : ResourcePath) : (k : FunctionKind) × FunctionDef k :=
  ⟨.plain, ⟨ref path, .plain #[.returnRun (.function (ref target))]⟩⟩

private def input := #[
  leaf "__oria/leaf-a", leaf "__oria/leaf-b",
  call "__oria/parent-a" "__oria/leaf-a", call "__oria/parent-b" "__oria/leaf-b",
  call "left" "__oria/parent-a", call "right" "__oria/parent-b",
  leaf "__oria/load", leaf "__oria/tick"]

/-- Sharing a leaf exposes equivalent callers in the next round. Public identities remain. -/
example : (Optimize.Sharing.run input).size = 6 := by native_decide

example : (Optimize.Sharing.run input).toList.map (fun ⟨_, d⟩ => d.ref.id.path.val) =
    ["__oria/leaf-a", "__oria/parent-a", "left", "right", "__oria/load", "__oria/tick"] := by
  native_decide

private def template {s : MacroSchema} (path : ResourcePath) (nonempty : 0 < s.fields.length)
    (numeric : (s.fields.get ⟨0, nonempty⟩).ty = .i32) : (k : FunctionKind) × FunctionDef k :=
  ⟨.macro s, ⟨ref path, .macro #[.macro (.ofCommand
    (.data (.get (.index ⟨"sharing:data", .key "items"⟩ ⟨0, nonempty⟩ [] numeric)))
    (by simp [Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]))]⟩⟩

private def one : MacroSchema := .ofFields [⟨.i32, .i32⟩]
private def two : MacroSchema := .ofFields [⟨.i32, .i32⟩, ⟨.i32, .i32⟩]

/-- Equal emitted parameter text retains distinct macro calling contracts. -/
example : (Optimize.Sharing.run #[
    template (s := one) "__oria/macro-a" (by simp [one]) (by simp [one]),
    template (s := one) "__oria/macro-b" (by simp [one]) (by simp [one]),
    template (s := two) "__oria/macro-c" (by simp [two]) (by simp [two])]).size = 2 := by native_decide

example {mode : Mode} (c : Command mode) : c.mapFunctions (fun r => r) = c :=
  Command.mapFunctions_id c

end Oria.Proofs.Sharing
