module

import Oria.Meta.McFunction
meta import Oria.Meta.McFunction

namespace Oria.Proofs.McFunction

open Oria Oria.IR
open Lean Lean.Elab

@[mcfunction]
def chooseAndIncrement
    (condition : Val Bool)
    (left right : Val Int32) :
    Prog .pure Int32 :=
  Prog.bind
    (Prog.branch condition (Prog.pure left) (Prog.pure right))
    fun value => Prog.pure (I32.add value (I32.lit 1))

example : chooseAndIncrement.signature =
    { args := [.bool, .i32, .i32], result := .i32, grade := .pure } := rfl

example : DeclRef chooseAndIncrement.signature :=
  chooseAndIncrement.ref

example :
    Val Bool → Val Int32 → Val Int32 → Prog .pure Int32 :=
  chooseAndIncrement.call

/--
error: declaration
-/
#guard_msgs(error, substring := true) in
attribute [mcfunction] chooseAndIncrement

run_cmd
  let env ← getEnv
  let some entry := McFunctionRegistry.find? env ``chooseAndIncrement
    | throwError "mcfunction declaration is absent from the registry"
  unless entry.signature == chooseAndIncrement.signature do
    throwError "mcfunction registry contains the wrong signature"
  match McFunctionRegistry.elaborate env ``chooseAndIncrement with
  | .error diagnostic =>
    throwError "mcfunction recipe failed: {repr diagnostic}"
  | .ok elaborated =>
      unless elaborated.signature == chooseAndIncrement.signature do
        throwError "elaborated definition has the wrong signature"

end Oria.Proofs.McFunction
