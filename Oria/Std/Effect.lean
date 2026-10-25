module

public import Oria.Std.Command.Arg
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Status effects

`give` uses Minecraft's default duration: 30 seconds for ordinary effects and 1 tick for
instantaneous effects. `giveFor` accepts a finite native count or infinite duration, an
amplifier, and a particle-visibility flag. Finite counts mean seconds for ordinary effects
and ticks for instantaneous effects. `clear` removes one effect or all effects.

Only living entities can have effects. Results count entities whose effect state changed;
an empty selection or a selection with no changed living entity fails. Ordinary do notation
propagates failure, and discard permits repeated cleanup. Effect IDs are host resource names;
finite counts and amplifiers may be runtime I32 values.
-/

namespace Oria.Std.Effect

open Oria.Std.Command.Arg

/-- Require the target selection's context and retain the world, score-access, and randomness
effect bound. The optional native source entity supplies attribution when present. -/
@[expose] public def grade (targets : Target := .self) : Grade :=
  ⟨targets.requirements, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

/-- Give a registered effect with native default duration, amplifier zero, and visible
particles. Return the number of changed living entities; fail if none change. An existing
stronger or equally long effect may make the operation unchanged. -/
public def give (targets : Target) (effect : ResourceId) : Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.effectGive, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.effectGive.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode effect) .nil)

/-- Give an effect with an explicit duration. Minecraft accepts finite counts from 1 to
1000000 and amplifiers from 0 to 255; the amplifier is zero-based. The flag hides particles
and the HUD icon. Counts are seconds for ordinary effects and ticks for instantaneous effects.
Native bounds are checked during parsing, after substitution for dynamic arguments.
Success and failure follow give; the result is the changed-entity count.

```lean
open Oria Oria.Std
example (seconds : Val Int32) :=
  Effect.giveFor .self "minecraft:speed" (.finite (.dynamic seconds)) (.static 1) true
example := Effect.giveFor .self "minecraft:night_vision" .infinite
```
-/
public def giveFor (targets : Target) (effect : ResourceId) (duration : Duration)
    (amplifier : Scalar := .static 0) (hideParticles : Bool := false) :
    Prog (grade targets) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.effectGiveFor, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.effectGiveFor.call <|
      .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode effect) <|
        .cons (Oria.Command.encode duration) <| .cons (Oria.Command.encode amplifier) <|
          .cons (Oria.Command.encode hideParticles) .nil)

/-- Remove one effect, or all effects when omitted, from the selected living entities.
The target defaults to self. Return the number of entities changed, not the number of effects
removed. Fail if no selected living entity has a matching active effect. -/
public def clear (targets : Target := .self) (effect : Option ResourceId := none) :
    Prog (grade targets) Int32 :=
  match effect with
  | none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.effectClear, Req.none, BitVec.or_assoc] using
        (Oria.Command.emit <| Command.Declarations.effectClear.call <|
          .cons (Oria.Command.encode targets) .nil)
  | some effect => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Target.requirements, Oria.Command.Call.grade, Oria.Command.Call.requirements,
        Oria.Command.Ref.call, Command.Declarations.effectClearOne, Req.none, BitVec.or_assoc] using
        (Oria.Command.emit <| Command.Declarations.effectClearOne.call <|
          .cons (Oria.Command.encode targets) <| .cons (Oria.Command.encode effect) .nil)

end Oria.Std.Effect
