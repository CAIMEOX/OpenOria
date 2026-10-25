module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Attribute

Operate on one living entity's registered attribute. Queries multiply the native Double
value by a scale and truncate toward zero to I32. Set, reset, add, and remove return 1.
A missing attribute/modifier, duplicate modifier, or ineligible target fails.
-/

namespace Oria.Std.Attribute
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Entity selection and attribute mutation effects. -/
@[expose] public def grade (target : Target) : Grade :=
  ⟨target.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Execute an attribute action. Modifier IDs are host resources; amounts and query scales
can be static fractions or dynamic I32 values. Native attribute clamping still applies. -/
public def run (target : Target) (id : ResourceId) (action : AttributeAction) :
    Prog (grade target) Int32 := do
  emit <| Command.Declarations.attributeRun.call <|
    .cons (encode target) <| .cons (encode id) <| .cons (encode action) <| .nil

end Oria.Std.Attribute
