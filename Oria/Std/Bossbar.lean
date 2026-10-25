module

public import Oria.Std.Command.Arg.Management
import Oria.Std.Command.Declarations.Management
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Bossbar

Custom boss bars are native server state. Get queries value, maximum, visibility, or player count.
Set uses a typed property; names and player selectors retain their interpretation requirements.
Unchanged updates can fail.
-/

namespace Oria.Std.Bossbar

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Native boss-bar management with optional text or selector requirements. -/
@[expose] public def grade (req : ReqRow := Req.none) : Grade :=
  ⟨req,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Create a bar and return the native total bar count. Duplicate IDs fail. -/
public def add (id : ResourceId) (name : TextComponent) :
    Prog (grade name.requirements) Int32 := do
  emit <| Command.Declarations.barAdd.call <| .cons (encode id) <| .cons (encode name) <| .nil

/-- Remove a bar; unknown IDs fail. Return the remaining bar count. -/
public def remove (id : ResourceId) : Prog grade Int32 := do
  emit <| Command.Declarations.barRemove.call <| .cons (encode id) <| .nil

/-- Return the number of custom boss bars, including successful zero. -/
public def list : Prog grade Int32 := do
  emit <| Command.Declarations.barList.call <| .nil

/-- Read a bar field. Visibility returns zero or one. -/
public def get (id : ResourceId) (field : BarField) : Prog grade Int32 := do
  emit <| Command.Declarations.barGet.call <| .cons (encode id) <| .cons (encode field) <| .nil

/-- Update one property. Values must be nonnegative and maxima positive; dynamic bounds
are parsed at invocation. Player replacement may clear the viewer set. -/
public def set (id : ResourceId) (property : BarProperty) :
    Prog (grade property.requirements) Int32 := do
  emit <| Command.Declarations.barSet.call <| .cons (encode id) <| .cons (encode property) <| .nil

end Oria.Std.Bossbar
