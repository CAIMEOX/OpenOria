module

public import Oria.IR.DP121.Syntax

namespace Oria.Target.DP121

/-- Rewrite structured references, preserving each call's kind and macro schema. -/
public def Command.mapFunctions {mode : Mode}
    (f : {k : FunctionKind} → FunctionRef k → FunctionRef k) : Command mode → Command mode
  | .function ref => .function (f ref)
  | .schedule ref => .schedule (f ref)
  | .commandLimit => .commandLimit
  | .functionWithStorage ref source => .functionWithStorage (f ref) source
  | .execute chain ref => .execute chain (f ref)
  | .when p c next => .when p c (next.mapFunctions f)
  | .store k target next => .store k target (next.mapFunctions f)
  | .returnRun next => .returnRun (next.mapFunctions f)
  | .scoreboard op => .scoreboard op
  | .data op => .data op
  | .invoke request => .invoke request
  | .native request => .native request
  | .returnValue value => .returnValue value
  | .returnFail => .returnFail

/-- Function renaming cannot add or remove a macro parameter occurrence. -/
@[simp] public theorem Command.parameterCount_mapFunctions {mode : Mode}
    (f : {k : FunctionKind} → FunctionRef k → FunctionRef k) (command : Command mode) :
    (command.mapFunctions f).parameterCount = command.parameterCount := by
  induction command <;> simp_all [mapFunctions, parameterCount]

@[simp] public theorem Command.mapFunctions_id {mode : Mode} (command : Command mode) :
    command.mapFunctions (fun ref => ref) = command := by
  induction command <;> simp_all [mapFunctions]

/-- Map calls on both static and macro-prefixed lines without changing their scopes. -/
public def FunctionBody.mapFunctions {kind : FunctionKind}
    (f : {k : FunctionKind} → FunctionRef k → FunctionRef k) : FunctionBody kind → FunctionBody kind
  | .plain commands => .plain (commands.map (·.mapFunctions f))
  | .macro lines => .macro (lines.map fun
      | .static command => .static (command.mapFunctions f)
      | .macro line => .macro (.ofCommand (line.command.mapFunctions f) (by simpa using line.used)))

end Oria.Target.DP121
