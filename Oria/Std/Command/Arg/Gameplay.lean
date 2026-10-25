module

public import Oria.Std.Command.Arg.Text

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

namespace Oria.Std.Command.Arg

open Oria.Command (GameMode)

public instance : Oria.Command.ArgCodec GameMode where
  key := ⟨`minecraft.argument.gamemode⟩
  encode value := .token value.token

@[simp] public theorem GameMode.encode_requirements (value : GameMode) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem GameMode.encode_fragment_requirements (value : GameMode) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

/-- Experience operation unit. -/
public inductive ExperienceUnit where
  /-- points. -/
  | points
  /-- levels. -/
  | levels
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec ExperienceUnit where
  key := ⟨`minecraft.argument.experienceunit⟩
  encode value := .token (match value with
    | .points => "points"
    | .levels => "levels")

@[simp] public theorem ExperienceUnit.encode_requirements (value : ExperienceUnit) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem ExperienceUnit.encode_fragment_requirements (value : ExperienceUnit) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl


/-- One registry resource or the native wildcard. -/
public inductive ResourceSet where
  /-- Every resource in the receiving command's registry. -/
  | all
  /-- One host resource ID. -/
  | one : ResourceId → ResourceSet

public instance : Oria.Command.ArgCodec ResourceSet where
  key := ⟨`minecraft.argument.resource_set⟩
  encode
    | .all => .token "*"
    | .one id => (Oria.Command.encode id).fragment

@[simp] public theorem ResourceSet.encode_requirements (value : ResourceSet) :
    (Oria.Command.encode value).requirements = Req.none := by cases value <;> rfl

@[simp] public theorem ResourceSet.encode_fragment_requirements (value : ResourceSet) :
    (Oria.Command.encode value).fragment.requirements = Req.none := value.encode_requirements

/-- Advancement traversal or a single criterion. Criterion text is a native greedy argument. -/
public inductive AdvancementScope where
  /-- All advancements. -/
  | everything
  /-- Only this advancement, optionally selecting one criterion. -/
  | only : ResourceId → Option Oria.Command.Inline → AdvancementScope
  /-- The advancement and its descendants. -/
  | «from» : ResourceId → AdvancementScope
  /-- The advancement and its ancestors. -/
  | until : ResourceId → AdvancementScope
  /-- Ancestors, the advancement, and descendants. -/
  | through : ResourceId → AdvancementScope

public instance : Oria.Command.ArgCodec AdvancementScope where
  key := ⟨`minecraft.argument.advancement_scope⟩
  encode scope :=
    let f : Oria.Command.Fragment EncodedVal := match scope with
      | .everything => .token "everything"
      | .only id criterion => .spaced ([.token "only", (Oria.Command.encode id).fragment] ++
          criterion.toList.map (fun c => .inline c))
      | .from id => .spaced [.token "from", (Oria.Command.encode id).fragment]
      | .until id => .spaced [.token "until", (Oria.Command.encode id).fragment]
      | .through id => .spaced [.token "through", (Oria.Command.encode id).fragment]
    ⟨f.segments, Req.none⟩

@[simp] public theorem AdvancementScope.encode_requirements (scope : AdvancementScope) :
    (Oria.Command.encode scope).requirements = Req.none := rfl

@[simp] public theorem AdvancementScope.encode_fragment_requirements (scope : AdvancementScope) :
    (Oria.Command.encode scope).fragment.requirements = Req.none := rfl

/-- Explicit damage type and optional location or entity attribution. -/
public inductive DamageCause where
  /-- A damage type without attribution. -/
  | type : ResourceId → DamageCause
  /-- A damage type attributed to a position. -/
  | «at» : ResourceId → Vec3 → DamageCause
  /-- Direct attacker, optionally with a causing entity. -/
  | «by» : ResourceId → Target → Option Target → DamageCause

public instance : Oria.Command.ArgCodec DamageCause where
  key := ⟨`minecraft.argument.damage_cause⟩
  encode
    | .type id => (Oria.Command.encode id).fragment
    | .at id p => .spaced [(Oria.Command.encode id).fragment, .token "at", (Oria.Command.encode p).fragment]
    | .by id direct cause => .spaced
        ([(Oria.Command.encode id).fragment, .token "by", (Oria.Command.encode direct).fragment] ++
          cause.toList.flatMap (fun c => [.token "from", (Oria.Command.encode c).fragment]))

/-- Requirements of attributed positions and entities. -/
@[expose] public def DamageCause.requirements (cause : DamageCause) : ReqRow :=
  (Oria.Command.encode cause).requirements

end Oria.Std.Command.Arg
