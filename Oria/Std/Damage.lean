module

public import Oria.Std.Command.Arg.Gameplay
import Oria.Std.Command.Declarations.Player
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Damage

Damage addresses one entity, with an optional registered damage type and source attribution. Amounts
use native nonnegative Float32 parsing. The command returns 1 when native damage handling accepts
the hit and fails otherwise.
-/

namespace Oria.Std.Damage

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Damage reads the dimension, target, and any source-attribution requirements. -/
@[expose] public def grade (target : Target) (cause : Option DamageCause := none) : Grade :=
  ⟨Req.dimension ||| target.requirements ||| (cause.map DamageCause.requirements).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.chat ||| Eff.failure⟩

/-- Apply damage. Omitted attribution selects native generic damage. Amount and source
coordinates can contain dynamic I32 values; static fractions reuse Decimal. -/
public def apply (target : Target) (amount : Decimal) (cause : Option DamageCause := none) :
    Prog (grade target cause) Int32 :=
  match cause with
  | none => do
      emit <| Command.Declarations.damage.call <| .cons (encode target) <| .cons (encode amount) <| .nil
  | some cause => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, DamageCause.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.Ref.call, Command.Declarations.damageFrom,
        Req.none, BitVec.or_assoc] using
        (emit <| Command.Declarations.damageFrom.call <| .cons (encode target) <|
          .cons (encode amount) <| .cons (encode cause) <| .nil)

end Oria.Std.Damage
