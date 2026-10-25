module

public import Oria.IR.DP121.Program
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

namespace Oria.Lower.DP121.Cost

open Oria.Target.DP121

private abbrev Definitions := Std.HashMap String ((k : FunctionKind) × FunctionBody k)
private abbrev M := ReaderT (Definitions × Std.HashSet String) (StateT (Std.HashMap String Nat) (Except Diagnostic))

/- Lean's compiler estimators consume Lean IR. This model consumes structured DP121:
function entries, execute modifiers, command declarations, and compiler-owned fragments. -/
private def command {mode : Mode} (visit : String → M Nat) : Command mode → M Nat
  | .function ref | .functionWithStorage ref _ => visit ref.id.render
  | .execute _ _ => throw (.unboundedTaskRegion "execute context traversal")
  | .when _ _ next => (1 + ·) <$> command visit next
  | .store _ _ next | .returnRun next => (1 + ·) <$> command visit next
  | .invoke call => match call.resolved.resolved.decl.cost with
      | some n => pure n
      | none => throw (.unboundedTaskRegion call.resolved.ref.key.toString)
  | .native call => match call.cost with
      | some n => pure n
      | none => throw (.unboundedTaskRegion "native fragment")
  | .scoreboard _ | .data _ | .returnValue _ | .returnFail | .schedule _ | .commandLimit => pure 1

private def lines (visit : String → M Nat) : List (Command .plain) → M Nat
  | [] => pure 0
  | c :: cs => do
      let head ← command visit c
      match c with
      | .returnRun _ | .returnFail | .returnValue _ => return head
      | .when _ _ (.returnRun _) | .when _ _ .returnFail | .when _ _ (.returnValue _) =>
          return max head (1 + (← lines visit cs))
      | _ => return head + (← lines visit cs)

private def body {k : FunctionKind} (visit : String → M Nat) : FunctionBody k → M Nat
  | .plain values => lines visit values.toList
  | .macro values => values.toList.foldlM (fun cost line => do
      let added ← match line with
        | .static c => command visit c
        | .macro c => command visit c.command
      return cost + added) 0

private def function : Nat → Std.HashSet String → String → M Nat
  | 0, _, name => throw (.unboundedTaskRegion name)
  | fuel + 1, active, name => do
      if (← read).2.contains name then return 1
      if let some cost := (← get).get? name then return cost
      if active.contains name then throw (.unboundedTaskRegion name)
      let some ⟨_, value⟩ := (← read).1.get? name | throw (.unresolvedTargetFunction name)
      let cost ← body (function fuel (active.insert name)) value
      modify (·.insert name (1 + cost))
      return 1 + cost

/-- A finite upper bound between declared boundaries; executing cycles require a checkpoint. -/
public def bound (definitions : Array ((k : FunctionKind) × FunctionDef k))
    (boundaries : Std.HashSet String) (ref : FunctionRef .plain) : Except Diagnostic Nat := do
  let table : Definitions := Std.HashMap.ofList
    (definitions.toList.map fun ⟨k, d⟩ => (d.ref.id.render, ⟨k, d.body⟩))
  let (cost, _) ← (function (definitions.size + 1) {} ref.id.render).run
    (table, boundaries.erase ref.id.render) |>.run {}
  return cost

end Oria.Lower.DP121.Cost
