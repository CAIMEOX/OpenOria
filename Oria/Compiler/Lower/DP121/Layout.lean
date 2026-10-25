module

public import Oria.IR.DP121.Syntax
import Init.Data.Vector.OfFn

namespace Oria.Lower.DP121

open Oria.Target.DP121

/-- Bounded ordinary homes, four working registers, and two return registers. -/
public structure Layout (k : Nat) where
  private mk ::
  registers : Vector Score k
  scratch : Vector Score 4
  results : Vector Score 2
  unique : (registers.toList ++ scratch.toList ++ results.toList).Nodup

namespace Layout

private def generated (objective : Oria.Command.Objective) (stem : String) (n : Nat) :
    Except Diagnostic (Vector Score n) :=
  Vector.ofFnM fun i => do
    let token ← Oria.Command.SyntaxToken.parse ("#" ++ stem ++ toString i.val)
    pure ⟨ScoreHolder.ofToken token, objective⟩

public def allocate (objective : Oria.Command.Objective) (k : Nat) :
    Except Diagnostic (Layout k) := do
  let registers ← generated objective "r" k
  let scratch ← generated objective "s" 4
  let results ← generated objective "ret" 2
  if unique : (registers.toList ++ scratch.toList ++ results.toList).Nodup then
    pure ⟨registers, scratch, results, unique⟩
  else throw (.invalidCommandToken "generated scoreboard register bank")

public theorem register_ne_scratch {k : Nat} (layout : Layout k) (r : Fin k) (t : Fin 4) :
    layout.registers[r] ≠ layout.scratch[t] := by
  have disjoint := (List.nodup_append.mp (List.nodup_append.mp layout.unique).1).2.2
  exact disjoint _ (by simp) _ (by simp)

public theorem register_ne_result {k : Nat} (layout : Layout k) (r : Fin k) (v : Fin 2) :
    layout.registers[r] ≠ layout.results[v] := by
  have disjoint := (List.nodup_append.mp layout.unique).2.2
  exact disjoint _ (by simp) _ (by simp)

end Layout
end Oria.Lower.DP121
