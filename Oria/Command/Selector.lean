module

public import Oria.Command.Range
public import Oria.Command.Argument

namespace Oria.Command

namespace Selector

/-- Positive or negated matching of a selector field. -/
public inductive Match (a : Type) where
  /-- Require the field to match. -/
  | include : a → Match a
  /-- Require the field not to match. -/
  | exclude : a → Match a

/-- Native selector ordering. Spatial orders read position and dimension. -/
public inductive Order where
  /-- Native traversal order. -/
  | arbitrary
  /-- Increasing distance from the execution position. -/
  | nearest
  /-- Decreasing distance from the execution position. -/
  | furthest
  /-- Randomized selection order. -/
  | random

/-- Match an advancement's completion state or a conjunction of named criteria. -/
public inductive Advancement where
  | completed : Bool → Advancement
  | criteria : List (Word × Bool) → Advancement

/-- Construction-time selector filters. Minecraft validates limits, intervals, and resources.
Repeated tags are conjunctive; a type filter and sort order each occur at most once. -/
public structure Filters where
  /-- Positive tags must be present; excluded tags must be absent. The empty string tests
  whether the entity has no tags. Planning checks Brigadier's unquoted-word alphabet. -/
  tags : List (Match String) := []
  /-- Team membership. An empty name selects entities without a team; excluding it selects
  entities with a team. Names use the same unquoted-word validation as tag filters. -/
  team : Option (Match String) := none
  /-- Include or exclude an entity type ID or entity-type tag. -/
  entityType : Option (Match ResourceOrTag) := none
  /-- Include or exclude an entity name using Brigadier quoted-string syntax. -/
  name : Option (Match String) := none
  /-- Player game mode. Non-player entities are excluded by the native filter. -/
  gameMode : Option (Match GameMode) := none
  /-- Inclusive player experience-level interval. -/
  level : Option (Range Int32) := none
  /-- Explicit origin X; omitted components come from the execution position. -/
  x : Option Float := none
  /-- Explicit origin Y. -/
  y : Option Float := none
  /-- Explicit origin Z. -/
  z : Option Float := none
  /-- Native selection-box X extent. Omitted extents are zero when any extent is present. -/
  dx : Option Float := none
  /-- Native selection-box Y extent. -/
  dy : Option Float := none
  /-- Native selection-box Z extent. -/
  dz : Option Float := none
  /-- Candidate pitch interval, with native wrapping at 180 degrees. -/
  xRotation : Option (Range Float) := none
  /-- Candidate yaw interval, with native wrapping at 180 degrees. -/
  yRotation : Option (Range Float) := none
  /-- Conjunctive predicates evaluated with each candidate's entity, origin, and level. -/
  predicates : List (Match ResourceId) := []
  /-- Conjunctive native NBT matches against each candidate's saved data. -/
  nbt : List (Match (Nbt.Value .compound)) := []
  /-- Player advancement requirements. Each resource and criterion should occur once. -/
  advancements : List (ResourceId × Advancement) := []
  /-- Native maximum result count, checked positive by Minecraft. -/
  limit : Option Int32 := none
  /-- Override the base selector's ordering. -/
  sort : Option Order := none
  /-- Conjunctive score requirements. Each objective should occur once. -/
  scores : List (Objective × Range Int32) := []
  /-- Inclusive distance in blocks, requiring the execution position and dimension. -/
  distance : Option (Range Float) := none

/-- Spatial filtering reads the current dimension. It reads the execution position when
an origin component is omitted. Candidate-local filters add no caller requirements. -/
@[expose] public def Filters.requirements (f : Filters) (ordered : Bool := false) : ReqRow :=
  let spatial := f.distance.isSome || f.dx.isSome || f.dy.isSome || f.dz.isSome ||
    (match f.sort with | some .nearest | some .furthest => true | some _ => false | none => ordered)
  let position := spatial && !(f.x.isSome && f.y.isSome && f.z.isSome)
  (if spatial || f.x.isSome || f.y.isSome || f.z.isSome then Req.dimension else Req.none) |||
    (if position then Req.position else Req.none)

private def separated {v : ObjTy → Type} (xs : List (Fragment v)) : Fragment v :=
  (xs.intersperse (.token ",")).foldl Fragment.append .empty

private def signed {a : Type} {v : ObjTy → Type}
    (encode : a → Fragment v) : Match a → Fragment v
  | .include value => encode value
  | .exclude value => .prepend "!" (encode value)

private def decimal {v : ObjTy → Type} (n : Float) : Fragment v :=
  ⟨[.literal (.decimal n)], Req.none⟩

private def quoted {v : ObjTy → Type} (s : String) : Fragment v :=
  ⟨[.literal (.quoted s)], Req.none⟩

private def boolean {v : ObjTy → Type} (b : Bool) : Fragment v :=
  .token (if b then "true" else "false")

private def advancement {v : ObjTy → Type} : Advancement → Fragment v
  | .completed b => boolean b
  | .criteria xs => .prepend "{" <|
      (separated (xs.map fun (key, b) =>
        (⟨[.literal (.unquoted key.text)], Req.none⟩ : Fragment v).append
          (.prepend "=" (boolean b)))).append (.token "}")

/-- Structured filters reuse fragments, native unquoted words, resource IDs, and numeric ranges. -/
public def Filters.fragment {v : ObjTy → Type} (filters : Filters) : Fragment v :=
  let tags : List (Fragment v) := filters.tags.map fun tag =>
    .prepend "tag=" (signed (fun s => ⟨[.literal (.unquoted s)], Req.none⟩) tag)
  let types : List (Fragment v) := filters.entityType.toList.map fun ty =>
    .prepend "type=" (signed ResourceOrTag.fragment ty)
  let limits : List (Fragment v) := filters.limit.toList.map fun n => .prepend "limit=" (.i32 n)
  let sorts : List (Fragment v) := filters.sort.toList.map fun order => .prepend "sort=" (.token (match order with
    | .arbitrary => "arbitrary" | .nearest => "nearest" | .furthest => "furthest" | .random => "random"))
  let scores : List (Fragment v) := if filters.scores.isEmpty then [] else
    [.prepend "scores={" ((separated (filters.scores.map fun (objective, bounds) =>
      (⟨[.literal (.unquoted objective.token.text)], Req.none⟩ : Fragment v).append
        ((Fragment.token "=").append (bounds.fragment Fragment.i32)))).append (.token "}"))]
  let distances : List (Fragment v) := filters.distance.toList.map fun range =>
    .prepend "distance=" (range.fragment decimal)
  let teams : List (Fragment v) := filters.team.toList.map fun team =>
    .prepend "team=" (signed (fun s => ⟨[.literal (.unquoted s)], Req.none⟩) team)
  let names := filters.name.toList.map fun n => .prepend "name=" (signed quoted n)
  let modes := filters.gameMode.toList.map fun m => .prepend "gamemode=" (signed (fun m => .token m.token) m)
  let levels := filters.level.toList.map fun r => .prepend "level=" (r.fragment Fragment.i32)
  let coords := ([("x=", filters.x), ("y=", filters.y), ("z=", filters.z),
    ("dx=", filters.dx), ("dy=", filters.dy), ("dz=", filters.dz)] : List (SyntaxToken × Option Float)).flatMap
      fun (key, val) => val.toList.map fun n => .prepend key (decimal n)
  let rotations := ([("x_rotation=", filters.xRotation), ("y_rotation=", filters.yRotation)] :
      List (SyntaxToken × Option (Range Float))).flatMap fun (key, val) =>
        val.toList.map fun r => .prepend key (r.fragment decimal)
  let predicates := filters.predicates.map fun p =>
    .prepend "predicate=" (signed (fun id => .token (.ofResourceId id)) p)
  let nbt := filters.nbt.map fun p => .prepend "nbt=" (signed Fragment.nbt p)
  let advancements := if filters.advancements.isEmpty then [] else
    [.prepend "advancements={" <| (separated (filters.advancements.map fun (id, a) =>
      (Fragment.token (.ofResourceId id)).append (.prepend "=" (advancement a)))).append (.token "}")]
  let fields := tags ++ teams ++ types ++ names ++ modes ++ levels ++ coords ++ rotations ++
    predicates ++ nbt ++ advancements ++ limits ++ sorts ++ scores ++ distances
  let body := if fields.isEmpty then Fragment.empty
    else (Fragment.token "[").append ((separated fields).append (.token "]"))
  { body with requirements := filters.requirements }

end Selector

/-- Entity selector descriptions shared by commands and execution scopes. -/
public inductive Selector where
  /-- The current executor. -/
  | self (filters : Selector.Filters := {})
  /-- Online players. -/
  | allPlayers (filters : Selector.Filters := {})
  /-- Entities in the current dimension. -/
  | allEntities (filters : Selector.Filters := {})
  /-- The nearest player. -/
  | nearestPlayer (filters : Selector.Filters := {})
  /-- The nearest entity. -/
  | nearestEntity (filters : Selector.Filters := {})
  /-- A random player. -/
  | randomPlayer (filters : Selector.Filters := {})
  /-- Native text with a conservative context contract. -/
  | query : Inline → Selector

namespace Selector

/-- Escape hatch for native selector syntax with conservative context requirements. -/
@[expose] public def ofString (text : String) (valid : Inline.Valid text := by native_decide) : Selector :=
  .query (.ofString text valid)

/-- Compose base-selector requirements with the structured filters' requirements. -/
@[expose] public def requirements : Selector → ReqRow
  | .self f => Req.executor ||| f.requirements
  | .allPlayers f | .randomPlayer f => f.requirements
  | .allEntities f => Req.dimension ||| f.requirements
  | .nearestPlayer f | .nearestEntity f => Req.dimension ||| f.requirements true
  | .query _ => Req.all

/-- Encode one selector, retaining its computed context contract in the fragment. -/
@[expose] public def fragment {v : ObjTy → Type} (selector : Selector) : Fragment v :=
  { segments := private_decl% (
      let body : Fragment v := match selector with
        | .self f => .prepend "@s" f.fragment
        | .allPlayers f => .prepend "@a" f.fragment
        | .allEntities f => .prepend "@e" f.fragment
        | .nearestPlayer f => .prepend "@p" f.fragment
        | .nearestEntity f => .prepend "@n" f.fragment
        | .randomPlayer f => .prepend "@r" f.fragment
        | .query text => .inline text
      body.segments)
    requirements := selector.requirements }

@[simp] public theorem fragment_requirements {v : ObjTy → Type} (selector : Selector) :
    (selector.fragment (v := v)).requirements = selector.requirements := rfl

end Selector

end Oria.Command
