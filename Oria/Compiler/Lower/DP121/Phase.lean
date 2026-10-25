module

public import Oria.IR.DP121.Program
public import Oria.Runtime.Phase

namespace Oria.Lower.DP121.Phase

open Oria.Target.DP121

private def score (objective : Oria.Command.Objective) : Score :=
  ⟨.ofToken "#phase", objective⟩

/-- Reject reentry before touching registers, panic state, or either arena. A missing
score is idle during the first load; load then initializes it explicitly. -/
public def guard (objective : Oria.Command.Objective) : Command .plain :=
  .when .positive (.matches (score objective) (.atLeast 1)) .returnFail

public def set (objective : Oria.Command.Objective) (phase : Oria.Runtime.Phase) : Command .plain :=
  .scoreboard (.set (score objective) phase.code)

public def leave (objective : Oria.Command.Objective) : Command .plain :=
  set objective .idle

/-- A suspended task retains objects outside the persistent root set. -/
public def quiescent (objective : Oria.Command.Objective) : List (Command .plain) :=
  [guard objective, .when .positive
    (.matches ⟨.ofToken "#task.phase", objective⟩ (.atLeast 1)) .returnFail]

end Oria.Lower.DP121.Phase
