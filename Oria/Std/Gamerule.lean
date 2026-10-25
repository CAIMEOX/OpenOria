module

public import Oria.Std.Command.Arg.Gamerule
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Gamerule

Rule descriptors fix Boolean or Scalar assignment types. Minecraft checks numeric ranges
and rejects unchanged assignments. Query and set return the native value, with false as
successful zero. Both read the execution dimension's game rules.
-/

namespace Oria.Std.Gamerule
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension requirements and observable rule changes. -/
@[expose] public def grade (req : ReqRow := Req.none) : Grade :=
  ⟨Req.dimension ||| req,
    Eff.world ||| Eff.failure⟩

/-- Query the value of a registered rule. -/
public def get {a : Type} (rule : GameRule a) : Prog grade Int32 := do
  emit <| Command.Declarations.ruleGet.call <|
    .cons (encode rule.name) <| .nil

/-- Assign a rule, preserving native bounds and unchanged-state failures.
Integer rules accept dynamic I32 values; Boolean values are host choices. -/
private def assign (update : RuleUpdate) : Prog (grade update.requirements) Int32 := do
  emit <| Command.Declarations.ruleSet.call <|
    .cons (encode update) <| .nil

/-- Assign a typed rule. Integer assignments may contain runtime I32 values; Boolean
assignments are host choices. Minecraft checks bounds and rejects unchanged values. -/
public def set {a : Type} [Oria.Command.ArgCodec a] (rule : GameRule a) (value : a) :
    Prog (grade (encode value).requirements) Int32 := by
  simpa using assign (rule.assign value)

end Oria.Std.Gamerule
