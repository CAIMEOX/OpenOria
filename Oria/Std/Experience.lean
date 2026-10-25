module

public import Oria.Std.Command.Arg.Gameplay
import Oria.Std.Command.Declarations.Player
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Experience

Add accepts signed values. Set requires nonnegative amounts; point assignment must fit each player's
current level. Query requires one player and returns points within the level or the level count.
-/

namespace Oria.Std.Experience

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Player-selection requirements and gameplay effects. -/
@[expose] public def grade (targets : Players) : Grade :=
  ⟨targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩

/-- Add signed points or levels; numeric values may be dynamic. Return the native target count. -/
public def add (targets : Players) (amount : Scalar) (unit : ExperienceUnit := .points) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.experienceAdd.call <|
    .cons (encode targets) <| .cons (encode amount) <| .cons (encode unit) <| .nil

/-- Set points or levels. Native per-player point-capacity checks may reject the operation. -/
public def set (targets : Players) (amount : Scalar) (unit : ExperienceUnit := .points) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.experienceSet.call <|
    .cons (encode targets) <| .cons (encode amount) <| .cons (encode unit) <| .nil

/-- Query a single player's points within the current level or their level count.
Minecraft enforces single-player selection. -/
public def query (target : Players := .self) (unit : ExperienceUnit := .points) :
    Prog (grade target) Int32 := do
  emit <| Command.Declarations.experienceQuery.call <|
    .cons (encode target) <| .cons (encode unit) <| .nil

end Oria.Std.Experience
