module

public import Oria
meta import Lean.Elab.GuardMsgs

open Oria
open Lean Lean.Elab

public axiom unavailable : Prog .pure Int32

/--
error: `unavailable` not supported by code generator
-/
#guard_msgs(error, substring := true) in
@[mcfunction]
def broken : Prog .pure Int32 :=
  unavailable

run_cmd
  let env ← Lean.getEnv
  for name in [``broken ++ `signature, ``broken ++ `ref, ``broken ++ `call] do
    if env.contains name then
      throwError "failed mcfunction leaked generated declaration `{name}`"

  if McFunctionRegistry.find? env ``broken |>.isSome then
    throwError "failed mcfunction leaked into the registry"

  if Lean.isDeclMeta env ``broken then
    throwError "failed mcfunction leaked compile-time IR visibility"
