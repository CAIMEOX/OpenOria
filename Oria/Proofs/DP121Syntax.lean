module

import Oria.IR.DP121.Syntax

namespace Oria.Proofs.DP121Syntax

open Oria Oria.Command Oria.Target.DP121

def oneI32 : MacroSchema :=
  .ofFields [{ ty := .i32, codec := .i32 }]

def firstParameter : Piece (.macro oneI32) :=
  .parameter ⟨0, by simp [oneI32]⟩

theorem first_parameter_field :
    oneI32.fields.get ⟨0, by simp [oneI32]⟩ =
      { ty := .i32, codec := .i32 } := by
  simp [oneI32]

theorem plain_piece_has_no_parameter (piece : Piece .plain) :
    piece.parameterCount = 0 := by
  cases piece <;> rfl

def typedMacroCall {schema : MacroSchema} {mode : Mode}
    (callee : FunctionRef (.macro schema))
    (source : MacroSource schema) : Command mode :=
  .functionWithStorage callee source

theorem macro_line_uses_parameter {schema : MacroSchema} (line : MacroLine schema) :
    0 < line.command.parameterCount :=
  line.used

def wrapPreservesMode {mode : Mode}
    (sink : Capture) (command : Command mode) : Command mode :=
  sink.wrap command

theorem first_parameter_key :
    (oneI32.parameterKey ⟨0, by simp [oneI32]⟩).text = "p0" := by
  simp only [MacroSchema.parameterKey]
  native_decide

theorem range_has_bound (range : IntRange) :
    range.lower.isSome ∨ range.upper.isSome :=
  range.bounded

theorem between_is_ordered (lower upper : Int32) (ordered : lower ≤ upper) :
    lower ≤ upper := by
  simpa [BoundsOrdered] using (IntRange.between lower upper ordered).ordered

theorem effect_shape {mode : Mode} (command : Command mode) :
    (({} : Capture)).wrap command = command := rfl

theorem status_shape {mode : Mode} (status : Score) (command : Command mode) :
    (({ success := some status } : Capture)).wrap command =
      .store .success (.score status) command := rfl

theorem result_shape {mode : Mode} (result : Score) (command : Command mode) :
    ({ result := some result } : Capture).wrap command =
      .store .result (.score result) command := rfl

theorem payload_shape {mode : Mode} (status result : Score) (command : Command mode) :
    (({ success := some status, result := some result } : Capture)).wrap command =
      .store .success (.score status) (.store .result (.score result) command) := rfl

def homogeneousI32List (values : Array Int32) :
    Nbt.Value .list :=
  .list (Nbt.Values.ofArray (values.map Nbt.Value.int))

end Oria.Proofs.DP121Syntax
