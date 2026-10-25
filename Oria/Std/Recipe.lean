module

public import Oria.Std.Command.Arg.Gameplay
import Oria.Std.Command.Declarations.Player
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Recipe

Give and take operate on one recipe ID or the native wildcard. They preserve Minecraft's
modification count and fail when no recipe progress changes or no players match.
-/

namespace Oria.Std.Recipe

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Player-selection requirements and recipe-book/gameplay effects. -/
@[expose] public def grade (targets : Players) : Grade :=
  ⟨targets.requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩

/-- Unlock one or all recipes. Recipe IDs must be present in the loaded registry. -/
public def give (targets : Players) (recipes : ResourceSet) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.recipeGive.call <|
    .cons (encode targets) <| .cons (encode recipes) <| .nil

/-- Remove one or all recipes from players' recipe books. -/
public def take (targets : Players) (recipes : ResourceSet) :
    Prog (grade targets) Int32 := do
  emit <| Command.Declarations.recipeTake.call <|
    .cons (encode targets) <| .cons (encode recipes) <| .nil

end Oria.Std.Recipe
