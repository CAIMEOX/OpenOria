module

public import Oria.Std.Command.Arg.Management
import Oria.Std.Command.Declarations.Management
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Team

Teams are native scoreboard state. Membership accepts names, entity selectors, or tracked-holder
wildcard selection. Typed properties cover colors, visibility, collision, friendly fire, and display
text. All operations preserve native result/failure behavior.
-/

namespace Oria.Std.Team

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Team management effects, including score writes and client-visible formatting. -/
@[expose] public def grade (req : ReqRow := Req.none) : Grade :=
  ⟨req,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Create a named team, optionally with a display component. Duplicate names fail;
success returns the total team count. -/
public def add (name : Oria.Command.Word) (display : Option TextComponent := none) :
    Prog (grade ((display.map TextComponent.requirements).getD Req.none)) Int32 :=
  match display with
  | none => do
      emit <| Command.Declarations.teamAdd.call <| .cons (encode name) <| .nil
  | some display => do
      emit <| Command.Declarations.teamAddNamed.call <|
        .cons (encode name) <| .cons (encode display) <| .nil

/-- Remove a team and return the remaining team count. Unknown names fail. -/
public def remove (name : Oria.Command.Word) : Prog grade Int32 := do
  emit <| Command.Declarations.teamRemove.call <| .cons (encode name) <| .nil

/-- Remove all members and return their count. An already-empty team fails. -/
public def empty (name : Oria.Command.Word) : Prog grade Int32 := do
  emit <| Command.Declarations.teamEmpty.call <| .cons (encode name) <| .nil

/-- Query total teams, or a named team's member count. Zero can be successful. -/
public def list (name : Option Oria.Command.Word := none) : Prog grade Int32 :=
  match name with
  | none => do
      emit <| Command.Declarations.teamList.call <| .nil
  | some name => do
      emit <| Command.Declarations.teamMembers.call <| .cons (encode name) <| .nil

/-- Join selected holders, defaulting to self. Return the selected-holder count;
rejoining the same team succeeds and preserves its membership. -/
public def join (name : Oria.Command.Word) (members : Holders := .one .self) :
    Prog (grade members.requirements) Int32 := do
  emit <| Command.Declarations.teamJoin.call <| .cons (encode name) <| .cons (encode members) <| .nil

/-- Remove selected holders from their teams and return the changed-holder count.
A named holder without a team yields a successful zero. -/
public def leave (members : Holders := .one .self) :
    Prog (grade members.requirements) Int32 := do
  emit <| Command.Declarations.teamLeave.call <| .cons (encode members) <| .nil

/-- Modify one team property. Most unchanged values fail; prefix and suffix retain native
success behavior. Successful zero values are ordinary command results. -/
public def modify (name : Oria.Command.Word) (property : TeamProperty) :
    Prog (grade property.requirements) Int32 := do
  emit <| Command.Declarations.teamModify.call <| .cons (encode name) <| .cons (encode property) <| .nil

end Oria.Std.Team
