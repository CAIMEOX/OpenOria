module

public import Oria.Std.Command.Arg.Generation
import Oria.Std.Command.Declarations.Generation
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Place

Feature, jigsaw, structure, and template placement all return 1 on native success.
Their native generators determine success; this result is not a changed-block count.
The default destination is BlockPos.here. Supplying absolute world coordinates removes the
execution-position requirement while retaining dimension.

Feature placement accepts named or inline descriptions and requires the surrounding 3 by 3
chunks to be loaded. Jigsaw and structure generation use world-generation rules and can fail
for a pool, connector, terrain, or generator that cannot produce a valid start. Template
settings supply rotation, mirror, integrity, seed, and strict placement in native order.
-/

namespace Oria.Std.Place
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Native placement effects and dependencies of the destination and description. -/
@[expose] public def grade (pos : BlockPos) (req : ReqRow := Req.none) : Grade :=
  ⟨Req.dimension ||| req ||| (encode pos).requirements,
    Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound ||| Eff.failure⟩

/-- Place a named or inline feature at the block position. Returns 1 if its generator
succeeds. The feature receives its placement world, origin, generator, and random source.
Static or dynamic NBT leaves use the shared feature/command fragment representation. -/
public def feature (value : Feature) (pos : BlockPos := .here) :
    Prog (grade pos value.requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, Oria.Command.Call.grade, Oria.Command.Call.requirements,
    Oria.Command.Ref.call, Command.Declarations.placeFeature, Req.none, BitVec.or_assoc] using
    (emit <| Command.Declarations.placeFeature.call <|
      .cons (encode value) <| .cons (encode pos) .nil)

/-- Generate a pool starting at the connector named target. Depth is parsed as an integer
in 1..20; it may be a runtime I32. Returns 1 on successful native generation.
The pool and connector are construction-time resource IDs. -/
public def jigsaw (pool target : ResourceId) (depth : Scalar) (pos : BlockPos := .here) :
    Prog (grade pos) Int32 := do
  emit <| Command.Declarations.placeJigsaw.call <|
    .cons (encode pool) <| .cons (encode target) <| .cons (encode depth) <| .cons (encode pos) .nil

/-- Generate a registered structure using the current world's generator, seed, and terrain.
Returns 1 if a valid structure start is generated. Native placement need not anchor the
structure's first block at the supplied position. -/
public def «structure» (id : ResourceId) (pos : BlockPos := .here) :
    Prog (grade pos) Int32 := do
  emit <| Command.Declarations.placeStructure.call <|
    .cons (encode id) <| .cons (encode pos) .nil

/-- Place a named structure template, returning 1 on native success. Missing templates and
unavailable chunks fail. Integrity is a Float32 probability in 0..1; zero can still succeed.
A nonzero seed selects repeatable native randomness; zero uses the native time-derived source.
Position, integrity, and seed can contain dynamic I32 holes. -/
public def template (id : ResourceId) (pos : BlockPos := .here) (settings : TemplateSettings := {}) :
    Prog (grade pos) Int32 := do
  emit <| Command.Declarations.placeTemplate.call <|
    .cons (encode id) <| .cons (encode pos) <| .cons (encode settings) .nil

end Oria.Std.Place
