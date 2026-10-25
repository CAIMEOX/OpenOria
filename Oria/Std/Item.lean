module

public import Oria.Std.Command.Arg.Item
import Oria.Std.Command.Declarations.Content
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Item

Transfer uses native replace, fill, or override distribution over slot sources. Modify
evaluates an item modifier per selected item. Minecraft constructs a slot context containing
the command origin, dimension, and container even for a literal slot range. External
definitions retain their additional requirements. Operations can update only part of a selection.
-/

namespace Oria.Std.Item
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Native slot-context construction plus inventory and optional source/modifier dependencies. -/
@[expose] public def grade (inventory : Inventory) (req : ReqRow := Req.none) : Grade :=
  ⟨(Req.dimension ||| Req.position) ||| (inventory.requirements ||| req), Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Transfer constructed or sourced items into selected slots. Replace retains unmatched
destination slots; fill repeats source entries; override clears the unmatched suffix.
Result and failure follow native slot updates, with no transactional rollback. -/
public def transfer (target : Inventory) (source : ItemSource) (mode : ItemDistribution := .replace) :
    Prog (grade target source.requirements) Int32 := do
  emit <| Command.Declarations.transferItems.call <|
    .cons (encode mode) <| .cons (encode target) <| .cons (encode source) <| .nil

/-- Apply a named, inline, or semantically constructed item modifier to the selected slots.
Native validation rejects unavailable slots or incompatible targets. -/
public def modify (target : Inventory) (modifier : ItemModifier) :
    Prog (grade target modifier.requirements) Int32 := do
  emit <| Command.Declarations.modifyItems.call <|
    .cons (encode target) <| .cons (encode modifier) <| .nil

end Oria.Std.Item
