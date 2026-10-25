module

public import Oria.Std.Command.Arg.Numeric
public import Oria.Command.Selector
public import Oria.Command.Argument
public import Oria.Command.Nbt

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Shared command arguments

These host types describe argument syntax and encode into command fragments during program
construction. `Scalar` distinguishes static I32 values from runtime `Val Int32` expressions.
Each dynamic component introduces its own macro argument; other static text in the same
argument remains literal.

`Target` describes entity targets, `Players` a player set, and `ScoreHolder` a score holder.
Each receiving command determines whether its target must be singular.
The first two accept `Command.Selector` descriptions with tag, type, score-range, limit,
distance, and ordering filters. Execute consumes the same selector type. Structured filters
retain their context requirements; raw native text has a conservative contract.
`Vec3.absolute` and `Vec3.relative` construct uniform world coordinates. `Vec3.world`
permits mixed absolute and relative coordinates; all three components of `Vec3.local`
use local coordinates. Numeric literals and runtime I32 expressions enter components directly;
`Decimal` retains the distinction between integer and fractional spelling.
An argument's `requirements` describe the execution
context it reads. Lean checks argument types during construction; Minecraft validates
selectors, ranges, and resources during native parsing and execution.

Applications use the command modules. Command library authors can reuse this module's
`ArgCodec` instances.
-/

namespace Oria.Std.Command.Arg

open Oria.Command (Objective ScoreOp)

/-- Native integer-range syntax with inclusive finite endpoints. Each command determines
whether singleton and unbounded ranges are accepted. -/
public abbrev Range := Oria.Command.Range Scalar

namespace Range

/-- Range encoding introduces no context requirements. -/
@[expose] public def requirements (_ : Range) : ReqRow := Req.none

end Range

/-- A command's player selection. Native selectors may match zero or more players;
each command determines how to interpret that selection. -/
public inductive Players where
  /-- The current executor. Requires executor context; the command also checks that it is a player. -/
  | self
  /-- All online players, emitting {lit}`@a`. -/
  | all
  /-- The nearest player, reading the current position and dimension. -/
  | nearest
  /-- A random player, emitting {lit}`@r`. -/
  | random
  /-- Native target text, conservatively requiring the full execution context. -/
  | select : Oria.Command.Inline → Players
  /-- Structured player selection. Minecraft validates player-only selection. -/
  | selector : Oria.Command.Selector → Players

/-- Construct a native player target. Checks single-line and macro-placeholder constraints;
Minecraft checks the target grammar. -/
@[expose] public def Players.ofString (text : String) (valid : Oria.Command.Inline.Valid text := by native_decide) :
    Players := .select (.ofString text valid)

/-- Named sequences selected for a random-state reset. -/
public inductive Sequences where
  /-- All sequences. Supplying seed settings also updates the server defaults. -/
  | all
  /-- One sequence identified by a resource name. The reset protocol reads the dimension's world seed. -/
  | one : ResourceId → Sequences

/-- Random-sequence seed and mixing settings. Flags are fixed at construction time;
the seed value may be computed dynamically. -/
public structure Seed where
  /-- Explicit seed, encoded as I32. -/
  value : Scalar
  /-- Mix in the world seed; enabled by default. -/
  includeWorldSeed : Bool := true
  /-- Mix in the sequence's resource name; enabled by default. -/
  includeSequenceId : Bool := true

/-- Entity target syntax shared by single-target and multiple-target commands.
Minecraft enforces the receiving command's cardinality requirement. -/
public inductive Target where
  /-- The current executor, emitting {lit}`@s`. -/
  | self
  /-- Native target text with conservative full context requirements. -/
  | select : Oria.Command.Inline → Target
  /-- Structured entity selection, with requirements derived from its base and filters. -/
  | selector : Oria.Command.Selector → Target

/-- Construct native entity target text. Checks text constraints; Minecraft checks selector
syntax and cardinality. -/
@[expose] public def Target.ofString (text : String) (valid : Oria.Command.Inline.Valid text := by native_decide) :
    Target := .select (.ofString text valid)

/-- One world-coordinate component in blocks, interpreted by Minecraft's native command rules. -/
public inductive WorldCoord where
  /-- An absolute coordinate in the current dimension. -/
  | absolute : Decimal → WorldCoord
  /-- An offset from the current position, using the {lit}`~` prefix. -/
  | relative : Decimal → WorldCoord

/-- Three-dimensional command coordinates. Each value may independently be static or dynamic.
World coordinates can mix absolute and relative components; local coordinates apply to all axes. -/
public inductive Vec3 where
  /-- World X, Y, Z coordinates, each an absolute value or relative offset. -/
  | world : WorldCoord → WorldCoord → WorldCoord → Vec3
  /-- Local left, up, forward offsets, reading executor, position, rotation, and anchor. -/
  | local : Decimal → Decimal → Decimal → Vec3

/-- Absolute world coordinates in blocks. Integer X/Z components use Minecraft's native
centering; decimal components retain their exact position. Runtime I32 components use macro holes. -/
@[expose] public def Vec3.absolute (x y z : Decimal) : Vec3 :=
  .world (.absolute x) (.absolute y) (.absolute z)

/-- World offsets from the execution position. Each component may be a numeric literal,
a host value, or a runtime I32 expression; encoding requires position context. -/
@[expose] public def Vec3.relative (x y z : Decimal) : Vec3 :=
  .world (.relative x) (.relative y) (.relative z)

/-- Plain score-holder names must neither start with a selector prefix nor be a wildcard. -/
@[expose] public def scoreHolderNameSafe (text : String) : Prop :=
  text.toList.head? ≠ some '@' ∧ text ≠ "*"

public instance (text : String) : Decidable (scoreHolderNameSafe text) := by
  unfold scoreHolderNameSafe
  infer_instance

/-- A plain or fake-player score-holder name with lexical and non-selector constraints.
String literals are checked against the expected type. -/
public structure ScoreHolderName where
  private mk ::
  /-- A validated command token. -/
  token : Oria.Command.SyntaxToken
  /-- The token is interpreted as a plain name. -/
  safe : scoreHolderNameSafe token.text := by decide

namespace ScoreHolderName

/-- Construct a score-holder name from text and proofs. Constants usually use the default
proof arguments or the checked string-literal interface. -/
public def ofString
    (text : String)
    (valid : Oria.Command.SyntaxToken.Valid text := by decide)
    (safe : scoreHolderNameSafe text := by decide) : ScoreHolderName :=
  { token := .ofString text valid
    safe := by simpa using safe }

/-- Check a name computed at construction time, reporting invalid tokens or selector forms. -/
public def parse (text : String) : Except Diagnostic ScoreHolderName := do
  let token ← Oria.Command.SyntaxToken.parse text
  if safe : scoreHolderNameSafe token.text then
    pure ⟨token, safe⟩
  else
    throw (.invalidCommandName text)

end ScoreHolderName

attribute [string_literal ScoreHolderName.ofString] ScoreHolderName

/-- A score holder, explicitly distinguishing the current entity from a plain name. -/
public inductive ScoreHolder where
  /-- The current executor, requiring executor context. -/
  | self
  /-- A validated plain or fake-player name. -/
  | named : ScoreHolderName → ScoreHolder

namespace ScoreHolder

/-- Parse construction-time text as a named holder. Use the explicit constructor for the executor. -/
public def parse (text : String) : Except Diagnostic ScoreHolder :=
  (ScoreHolderName.parse text).map named

end ScoreHolder

/-- A score location used by arithmetic, comparisons, and Execute result stores. -/
public structure ScoreSlot where
  /-- The score holder. -/
  holder : ScoreHolder
  /-- The owning objective, which must exist before use. -/
  objective : Objective

public instance : Oria.Command.ArgCodec Target where
  key := ⟨`minecraft.argument.entity_target⟩
  encode
    | .self =>
        .require Req.executor (.token "@s")
    | .select input => .require Req.all (.inline input)
    | .selector query => query.fragment

public instance : Oria.Command.ArgCodec Range where
  key := ⟨`minecraft.argument.int_range⟩
  encode range := range.fragment (fun value => (Oria.Command.encode value).fragment)

public instance : Oria.Command.ArgCodec ResourceId where
  key := ⟨`minecraft.argument.identifier⟩
  encode id := .token (.ofResourceId id)

public instance : Oria.Command.ArgCodec Oria.Command.Word where
  key := ⟨`minecraft.argument.word⟩
  encode word := ⟨[.literal (.unquoted word.text)], Req.none⟩

@[simp] public theorem Word.encode_requirements (word : Oria.Command.Word) :
    (Oria.Command.encode word).requirements = Req.none := rfl

@[simp] public theorem Word.encode_fragment_requirements (word : Oria.Command.Word) :
    (Oria.Command.encode word).fragment.requirements = Req.none := rfl

public instance : Oria.Command.ArgCodec Bool where
  key := ⟨`minecraft.argument.bool⟩
  encode value := .token (if value then "true" else "false")

@[simp] public theorem Bool.encode_requirements (value : Bool) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem Bool.encode_fragment_requirements (value : Bool) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

public instance : Oria.Command.ArgCodec Sequences where
  key := ⟨`minecraft.argument.random_sequences⟩
  encode
    | .all => .token "*"
    | .one id => .require Req.dimension (Oria.Command.encode id).fragment

public instance : Oria.Command.ArgCodec Seed where
  key := ⟨`minecraft.argument.random_seed⟩
  encode seed := .spaced [
    (Oria.Command.encode seed.value).fragment,
    (Oria.Command.encode seed.includeWorldSeed).fragment,
    (Oria.Command.encode seed.includeSequenceId).fragment]

public instance : Oria.Command.ArgCodec Players where
  key := ⟨`minecraft.argument.players⟩
  encode
    | .self => .require Req.executor (.token "@s")
    | .all => .token "@a"
    | .nearest => .require (Req.position ||| Req.dimension) (.token "@p")
    | .random => .token "@r"
    | .select input => .require Req.all (.inline input)
    | .selector query => query.fragment

public instance : Oria.Command.ArgCodec Nbt.Any where
  key := ⟨`minecraft.argument.snbt⟩
  encode value := .nbt value.2

namespace Nbt.Any

@[simp] public theorem encode_requirements (value : Nbt.Any) :
    (Oria.Command.encode value).requirements = Req.none := by
  rfl

@[simp] public theorem encode_fragment_requirements (value : Nbt.Any) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  rfl

end Nbt.Any

public instance : Oria.Command.ArgCodec WorldCoord where
  key := ⟨`minecraft.argument.world_coord⟩
  encode
    | .absolute value => (Oria.Command.encode value).fragment
    | .relative value =>
        .require Req.position <|
          .prepend "~" (Oria.Command.encode value).fragment

public instance : Oria.Command.ArgCodec Vec3 where
  key := ⟨`minecraft.argument.vec3⟩
  encode
    | .world x y z =>
        .spaced [
          (Oria.Command.encode x).fragment,
          (Oria.Command.encode y).fragment,
          (Oria.Command.encode z).fragment
        ]
    | .local x y z =>
        .require (Req.executor ||| Req.position ||| Req.rotation ||| Req.anchor) <| .spaced [
          .prepend "^" (Oria.Command.encode x).fragment,
          .prepend "^" (Oria.Command.encode y).fragment,
          .prepend "^" (Oria.Command.encode z).fragment
        ]

public instance : Oria.Command.ArgCodec ScoreHolder where
  key := ⟨`minecraft.argument.score_holder⟩
  encode
    | .self =>
        .require Req.executor (.token "@s")
    | .named name => .token name.token

public instance : Oria.Command.ArgCodec Objective where
  key := ⟨`minecraft.argument.objective⟩
  encode objective := .token objective.token

public instance : Oria.Command.ArgCodec ScoreOp where
  key := ⟨`minecraft.argument.score_operation⟩
  encode op := .token op.token

public instance : Oria.Command.ArgCodec ScoreSlot where
  key := ⟨`minecraft.argument.score_slot⟩
  encode slot := .spaced [
    (Oria.Command.encode slot.holder).fragment,
    (Oria.Command.encode slot.objective).fragment
  ]

namespace Range

@[simp] public theorem encode_requirements (value : Range) :
    (Oria.Command.encode value).requirements = Req.none := by
  cases value with
  | exact value =>
      change (Oria.Command.encode value).fragment.requirements = Req.none
      exact Scalar.encode_fragment_requirements value
  | between lo hi =>
      change (Oria.Command.encode lo).fragment.requirements |||
        (Req.none ||| (Oria.Command.encode hi).fragment.requirements) = Req.none
      simp [Scalar.encode_fragment_requirements, Req.none]
  | atLeast lo =>
      change (Oria.Command.encode lo).fragment.requirements ||| Req.none = Req.none
      simp [Scalar.encode_fragment_requirements, Req.none]
  | atMost hi =>
      change Req.none ||| (Oria.Command.encode hi).fragment.requirements = Req.none
      simp [Scalar.encode_fragment_requirements, Req.none]
  | any => rfl

end Range

namespace Range

@[simp] public theorem encode_fragment_requirements (value : Range) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  simpa [Oria.Command.EncodedArg.requirements] using encode_requirements value

end Range

namespace Objective

@[simp] public theorem encode_requirements (value : Objective) :
    (Oria.Command.encode value).requirements = Req.none := by
  rfl

@[simp] public theorem encode_fragment_requirements (value : Objective) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  rfl

end Objective

namespace ResourceId

@[simp] public theorem encode_requirements (value : ResourceId) :
    (Oria.Command.encode value).requirements = Req.none := by
  rfl

@[simp] public theorem encode_fragment_requirements (value : ResourceId) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  rfl

end ResourceId

namespace Seed

@[simp] public theorem encode_requirements (value : Seed) :
    (Oria.Command.encode value).requirements = Req.none := by
  cases value with
  | mk value includeWorldSeed includeSequenceId =>
      cases value <;>
        simp [Oria.Command.encode, Oria.Command.ArgCodec.encode,
          Oria.Command.EncodedArg.requirements, Req.none]

@[simp] public theorem encode_fragment_requirements (value : Seed) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  simpa [Oria.Command.EncodedArg.requirements] using encode_requirements value

end Seed

namespace ScoreOp

@[simp] public theorem encode_requirements (value : ScoreOp) :
    (Oria.Command.encode value).requirements = Req.none := by
  rfl

@[simp] public theorem encode_fragment_requirements (value : ScoreOp) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  rfl

end ScoreOp

namespace Target

/-- Context read by target encoding: the executor or the conservative requirements of raw text. -/
@[expose] public def requirements (value : Target) : ReqRow :=
  (Oria.Command.encode value).requirements

end Target

namespace Players

/-- Context read by player selection. -/
@[expose] public def requirements (value : Players) : ReqRow :=
  (Oria.Command.encode value).requirements

end Players

namespace Sequences

/-- Context used when resetting the selected random sequences. -/
@[expose] public def requirements (value : Sequences) : ReqRow :=
  (Oria.Command.encode value).requirements

@[simp] public theorem encode_fragment_requirements (value : Sequences) :
    (Oria.Command.encode value).fragment.requirements = requirements value := by
  rfl

end Sequences

namespace WorldCoord

/-- Relative coordinates require the current position; absolute components add no requirements. -/
@[expose] public def requirements (value : WorldCoord) : ReqRow :=
  (Oria.Command.encode value).requirements

end WorldCoord

namespace Vec3

/-- Combine component requirements, retaining position, rotation, executor, and anchor for local coordinates. -/
@[expose] public def requirements (value : Vec3) : ReqRow :=
  (Oria.Command.encode value).requirements

end Vec3

namespace ScoreHolder

/-- The current entity's score requires executor context; named scores do not. -/
@[expose] public def requirements (value : ScoreHolder) : ReqRow :=
  (Oria.Command.encode value).requirements

end ScoreHolder

namespace ScoreSlot

/-- Context requirements of a score location, determined by its holder. -/
@[expose] public def requirements (value : ScoreSlot) : ReqRow :=
  (Oria.Command.encode value).requirements

end ScoreSlot

end Oria.Std.Command.Arg
