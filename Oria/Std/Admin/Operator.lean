module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Operator permissions

Granting or revoking native operator status requires administrator permission (level 3).
The server's configured operator level determines the granted permissions.
-/

namespace Oria.Std.Admin.Operator
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Context used by profile selection, with permission-state mutation. -/
@[expose] public def grade (profiles : Profiles) : Grade :=
  ⟨profiles.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Grant operator status and return the changed profile count. Fails if all were operators. -/
public def grant (profiles : Profiles) : Prog (grade profiles) Int32 := do
  emit <| Command.Declarations.op.call <| .cons (encode profiles) <| .nil

/-- Revoke operator status, enforce whitelist admission, and return the changed profile count.
Fails if none was an operator. -/
public def revoke (profiles : Profiles) : Prog (grade profiles) Int32 := do
  emit <| Command.Declarations.deop.call <| .cons (encode profiles) <| .nil

end Oria.Std.Admin.Operator
