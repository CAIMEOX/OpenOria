module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Whitelist management

These commands require administrator permission (level 3). Native whitelist enforcement can
disconnect unlisted players when enabling, removing profiles, or reloading. Named profiles
can be offline; selector forms choose online profiles.
-/

namespace Oria.Std.Admin.Whitelist
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Profile selection and native admission-state effects. -/
@[expose] public def grade (req : ReqRow := Req.none) : Grade :=
  ⟨req, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Enable or disable admission filtering and return 1. An unchanged setting fails. -/
public def set (enabled : Bool) : Prog grade Int32 :=
  match enabled with
  | true => do emit <| Command.Declarations.whitelistOn.call <| .nil
  | false => do emit <| Command.Declarations.whitelistOff.call <| .nil

/-- Return the number of whitelist entries, including successful zero. Names are source feedback. -/
public def list : Prog grade Int32 := do
  emit <| Command.Declarations.whitelistList.call <| .nil

/-- Reload the native whitelist file, enforce admission, and return 1. -/
public def reload : Prog grade Int32 := do
  emit <| Command.Declarations.whitelistReload.call <| .nil

/-- Add selected profiles and return the newly added count. Fails if all are already listed
or native profile lookup fails. -/
public def add (profiles : Profiles) : Prog (grade profiles.requirements) Int32 := do
  emit <| Command.Declarations.whitelistAdd.call <| .cons (encode profiles) <| .nil

/-- Remove selected profiles, enforce admission, and return the removed count.
Fails if none of the profiles is listed. -/
public def remove (profiles : Profiles) : Prog (grade profiles.requirements) Int32 := do
  emit <| Command.Declarations.whitelistRemove.call <| .cons (encode profiles) <| .nil

end Oria.Std.Admin.Whitelist
