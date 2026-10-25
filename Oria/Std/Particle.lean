module

public import Oria.Std.Command.Arg.Control
import Oria.Std.Command.Declarations.Control
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Particle

Particle descriptions combine a registry ID with native NBT options. Static, mixed-field,
and runtime compound options reuse the NBT codec. Settings control the origin, delta,
speed, count, delivery mode, and viewers. Success counts delivered player packets.
-/

namespace Oria.Std.Particle
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Dimension, option-fragment, coordinate, and viewer requirements. -/
@[expose] public def grade (particle : ParticleSpec) (settings : ParticleSettings := {}) : Grade :=
  ⟨Req.dimension ||| (particle.requirements ||| settings.requirements),
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud ||| Eff.failure⟩

/-- Send particles; no eligible packet recipients fails. Count zero uses Minecraft's
directional-particle behavior. Rendering depends on client settings and resource availability. -/
public def send (particle : ParticleSpec) (settings : ParticleSettings := {}) :
    Prog (grade particle settings) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, ParticleSpec.requirements, ParticleSettings.requirements,
    Oria.Command.Call.grade, Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.particle, Req.none, BitVec.or_assoc] using
    (emit <| Command.Declarations.particle.call <|
      .cons (encode particle) <| .cons (encode settings) <| .nil)

end Oria.Std.Particle
