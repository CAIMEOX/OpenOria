module

public import Oria.Effect.Labels
public import Oria.Diagnostic
public import Oria.IR.Common.Signature
public import Oria.IR.Common.Type
public import Oria.Command.Literal
public meta import Oria.Data.StringLiteral

namespace Oria.Command

universe u₁ u₂

/-- Runtime serialization protocols understood by command lowering. -/
public inductive HoleCodec : ObjTy → Type where
  | i32 : HoleCodec .i32
  | nativeNbt {t : Option Nbt.Tag} : HoleCodec (.nbt t)
  deriving BEq, DecidableEq, Repr

/-- Open nominal identity for one command argument contract. Core never dispatches on this key. -/
public structure SlotKey where
  name : Lean.Name
  deriving BEq, DecidableEq, Hashable, Repr

namespace SyntaxToken

@[expose] public def Valid (text : String) : Prop :=
  text ≠ "" ∧
    ∀ character ∈ text.toList,
      32 ≤ character.toNat ∧
        character.toNat ≠ 127 ∧
          ¬character.isWhitespace ∧
            character ≠ '$' ∧ character ≠ '"' ∧ character ≠ '\\'

public instance (text : String) : Decidable (Valid text) := by
  unfold Valid
  infer_instance

end SyntaxToken

/-- One static command token. Whitespace is represented structurally by `Fragment.space`. -/
public structure SyntaxToken where
  text : String
  valid : SyntaxToken.Valid text := by decide
  deriving BEq, DecidableEq, Repr

namespace SyntaxToken

@[expose] public def ofString
    (text : String)
    (valid : Valid text := by decide) : SyntaxToken :=
  ⟨text, valid⟩

@[simp] public theorem ofString_text
    (text : String) (valid : Valid text) :
    (ofString text valid).text = text := rfl

public def parse (text : String) : Except Diagnostic SyntaxToken :=
  if valid : Valid text then
    .ok ⟨text, valid⟩
  else
    .error (.invalidCommandToken text)

end SyntaxToken

attribute [string_literal SyntaxToken.ofString] SyntaxToken

/-- Stable command-fragment primitives. Argument types are library extensions over this algebra. -/
public inductive Segment (v : ObjTy → Type) where
  | token : SyntaxToken → Segment v
  | space : Segment v
  | i32 : Int32 → Segment v
  | literal : Literal → Segment v
  | hole {a} : HoleCodec a → v a → Segment v

namespace Segment

@[expose] public def map {v w : ObjTy → Type} (η : ∀ {a}, v a → w a) : Segment v → Segment w
  | Segment.token value => Segment.token value
  | Segment.space => Segment.space
  | Segment.i32 value => Segment.i32 value
  | Segment.literal value => Segment.literal value
  | Segment.hole codec value => Segment.hole codec (η value)

/-- Transform a possible dynamic hole while preserving static segment syntax. -/
public def traverseK
    {v w : ObjTy → Type}
    {r : Type u₁}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (segment : Segment v)
    (next : Segment w → r) : r :=
  match segment with
  | .token value => next (.token value)
  | .space => next .space
  | .i32 value => next (.i32 value)
  | .literal value => next (.literal value)
  | .hole codec value => visit value fun transformed => next (.hole codec transformed)

public def All {v : ObjTy → Type} (p : ∀ {a}, v a → Prop) : Segment v → Prop
  | Segment.token _ | Segment.space | Segment.i32 _ | Segment.literal _ => True
  | Segment.hole _ value => p value

@[expose] public def AllT {v : ObjTy → Type} (p : ∀ {a}, v a → Type u₂) : Segment v → Type u₂
  | Segment.token _ | Segment.space | Segment.i32 _ | Segment.literal _ => PUnit
  | Segment.hole _ value => p value

@[expose] public def traverseKAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₂}
    {w : ObjTy → Type}
    {r : Type u₁}
    (visit : ∀ {a} (value : v a), p value → (w a → r) → r)
    (segment : Segment v)
    (evidence : segment.AllT p)
    (next : Segment w → r) : r :=
  match segment with
  | .token value => next (.token value)
  | .space => next .space
  | .i32 value => next (.i32 value)
  | .literal value => next (.literal value)
  | .hole codec value => visit value evidence fun transformed =>
      next (.hole codec transformed)

@[expose] public def mapAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₁}
    {q : ∀ {a}, v a → Type u₂}
    (transform : ∀ {a} (value : v a), p value → q value) :
    (segment : Segment v) → segment.AllT p → segment.AllT q
  | .token _, _ | .space, _ | .i32 _, _ | .literal _, _ => PUnit.unit
  | .hole _ value, evidence => transform value evidence

public def proveAll
    {m : Type → Type u₁}
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Prop}
    [Monad m]
    (prove : ∀ {a} (value : v a), m (PLift (p value))) :
    (segment : Segment v) → m (PLift (segment.All p))
  | Segment.token _ | Segment.space | Segment.i32 _ | Segment.literal _ => pure ⟨True.intro⟩
  | Segment.hole _ value => prove value

@[expose] public def holeCount {v : ObjTy → Type} : Segment v → Nat
  | Segment.token _ | Segment.space | Segment.i32 _ | Segment.literal _ => 0
  | Segment.hole _ _ => 1

@[simp] public theorem map_id {v : ObjTy → Type} (segment : Segment v) :
    segment.map (fun value => value) = segment := by
  cases segment <;> simp [map]

public theorem map_comp {v w x : ObjTy → Type}
    (left : ∀ {a}, v a → w a)
    (right : ∀ {a}, w a → x a)
    (segment : Segment v) :
    (segment.map left).map right = segment.map (fun value => right (left value)) := by
  cases segment <;> simp [map]

end Segment

/-- A partially static command fragment together with its execution-context requirements. -/
public structure Fragment (v : ObjTy → Type) where
  segments : List (Segment v)
  requirements : ReqRow

namespace Fragment

@[expose] public def empty {v : ObjTy → Type} : Fragment v :=
  ⟨[], Req.none⟩

@[expose] public def token {v : ObjTy → Type} (value : SyntaxToken) : Fragment v :=
  ⟨[.token value], Req.none⟩

@[expose] public def space {v : ObjTy → Type} : Fragment v :=
  ⟨[.space], Req.none⟩

@[expose] public def i32 {v : ObjTy → Type} (value : Int32) : Fragment v :=
  ⟨[.i32 value], Req.none⟩

@[expose] public def nbt {t : Nbt.Tag} {v : ObjTy → Type} (value : Nbt.Value t) : Fragment v :=
  ⟨[.literal (.nbt ⟨t, value⟩)], Req.none⟩

@[expose] public def inline {v : ObjTy → Type} (value : Inline) : Fragment v :=
  ⟨[.literal (.inline value)], Req.none⟩

@[expose] public def hole {a : ObjTy} {v : ObjTy → Type} (codec : HoleCodec a) (value : v a) : Fragment v :=
  ⟨[.hole codec value], Req.none⟩

@[expose] public def append {v : ObjTy → Type} (left right : Fragment v) : Fragment v :=
  ⟨left.segments ++ right.segments, left.requirements ||| right.requirements⟩

@[expose] public def prepend {v : ObjTy → Type} (token : SyntaxToken) (fragment : Fragment v) : Fragment v :=
  append (.token token) fragment

public instance {v : ObjTy → Type} : Append (Fragment v) where
  append := append

@[expose] public def spaced {v : ObjTy → Type} : List (Fragment v) → Fragment v
  | [] => empty
  | [fragment] => fragment
  | fragment :: rest => append (append fragment space) (spaced rest)

@[expose] public def require {v : ObjTy → Type} (requirements : ReqRow) (fragment : Fragment v) : Fragment v :=
  ⟨fragment.segments, requirements ||| fragment.requirements⟩

@[simp] public theorem requirements_empty {v : ObjTy → Type} : (empty : Fragment v).requirements = Req.none := rfl
@[simp] public theorem requirements_token {v : ObjTy → Type} (x : SyntaxToken) :
    (token x : Fragment v).requirements = Req.none := rfl
@[simp] public theorem requirements_space {v : ObjTy → Type} : (space : Fragment v).requirements = Req.none := rfl
@[simp] public theorem requirements_i32 {v : ObjTy → Type} (x : Int32) :
    (i32 x : Fragment v).requirements = Req.none := rfl
@[simp] public theorem requirements_nbt {t : Nbt.Tag} {v : ObjTy → Type} (x : Nbt.Value t) :
    (nbt x : Fragment v).requirements = Req.none := rfl
@[simp] public theorem requirements_inline {v : ObjTy → Type} (x : Inline) :
    (inline x : Fragment v).requirements = Req.none := rfl
@[simp] public theorem requirements_hole {a : ObjTy} {v : ObjTy → Type} (c : HoleCodec a) (x : v a) :
    (hole c x).requirements = Req.none := rfl
@[simp] public theorem requirements_append {v : ObjTy → Type} (x y : Fragment v) :
    (x.append y).requirements = x.requirements ||| y.requirements := rfl
@[simp] public theorem requirements_prepend {v : ObjTy → Type} (t : SyntaxToken) (x : Fragment v) :
    (prepend t x).requirements = x.requirements := by simp [prepend, Req.none]
@[simp] public theorem requirements_require {v : ObjTy → Type} (q : ReqRow) (x : Fragment v) :
    (require q x).requirements = q ||| x.requirements := rfl
@[simp] public theorem requirements_spaced {v : ObjTy → Type} (xs : List (Fragment v)) :
    (spaced xs).requirements = (xs.map (·.requirements)).foldr (· ||| ·) Req.none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases xs <;> simp_all [spaced, Req.none]

@[expose] public def map {v w : ObjTy → Type} (η : ∀ {a}, v a → w a) (fragment : Fragment v) : Fragment w :=
  ⟨fragment.segments.map (Segment.map η), fragment.requirements⟩

private def traverseSegmentsK
    {v w : ObjTy → Type}
    {r : Type u₁}
    (visit : ∀ {a}, v a → (w a → r) → r) :
    (segments : List (Segment v)) →
    (List (Segment w) → r) → r
  | [], next => next []
  | segment :: rest, next =>
      segment.traverseK visit fun transformed =>
        traverseSegmentsK visit rest fun transformedRest =>
          next (transformed :: transformedRest)

/-- Transform every dynamic hole from left to right. -/
public def traverseK
    {v w : ObjTy → Type}
    {r : Type u₁}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (fragment : Fragment v)
    (next : Fragment w → r) : r :=
  traverseSegmentsK visit fragment.segments fun segments =>
    next ⟨segments, fragment.requirements⟩

private def SegmentsAll {v : ObjTy → Type} (p : ∀ {a}, v a → Prop) : List (Segment v) → Prop
  | [] => True
  | segment :: rest => segment.All p ∧ SegmentsAll p rest

@[expose] public def SegmentsAllT {v : ObjTy → Type} (p : ∀ {a}, v a → Type u₂) :
    List (Segment v) → Type u₂
  | [] => PUnit
  | segment :: rest => segment.AllT p × SegmentsAllT p rest

public def All {v : ObjTy → Type} (p : ∀ {a}, v a → Prop) (fragment : Fragment v) : Prop :=
  SegmentsAll p fragment.segments

@[expose] public def AllT
    {v : ObjTy → Type}
    (p : ∀ {a}, v a → Type u₂) (fragment : Fragment v) : Type u₂ :=
  SegmentsAllT p fragment.segments

@[expose] public def traverseSegmentsKAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₂}
    {w : ObjTy → Type}
    {r : Type u₁}
    (visit : ∀ {a} (value : v a), p value → (w a → r) → r) :
    (segments : List (Segment v)) →
    SegmentsAllT p segments →
    (List (Segment w) → r) → r
  | [], _, next => next []
  | segment :: rest, evidence, next =>
      segment.traverseKAllT visit evidence.1 fun transformed =>
        traverseSegmentsKAllT visit rest evidence.2 fun transformedRest =>
          next (transformed :: transformedRest)

@[expose] public def mapSegmentsAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₁}
    {q : ∀ {a}, v a → Type u₂}
    (transform : ∀ {a} (value : v a), p value → q value) :
    (segments : List (Segment v)) →
      SegmentsAllT p segments → SegmentsAllT q segments
  | [], _ => PUnit.unit
  | segment :: rest, evidence =>
      (segment.mapAllT transform evidence.1,
        mapSegmentsAllT transform rest evidence.2)

@[expose] public def mapAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₁}
    {q : ∀ {a}, v a → Type u₂}
    (transform : ∀ {a} (value : v a), p value → q value)
    (fragment : Fragment v) : fragment.AllT p → fragment.AllT q :=
  mapSegmentsAllT transform fragment.segments

@[expose] public def traverseKAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₂}
    {w : ObjTy → Type}
    {r : Type u₁}
    (visit : ∀ {a} (value : v a), p value → (w a → r) → r)
    (fragment : Fragment v)
    (evidence : fragment.AllT p)
    (next : Fragment w → r) : r :=
  traverseSegmentsKAllT visit fragment.segments evidence fun segments =>
    next ⟨segments, fragment.requirements⟩

private def proveSegments
    {m : Type → Type u₁}
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Prop}
    [Monad m]
    (prove : ∀ {a} (value : v a), m (PLift (p value))) :
    (segments : List (Segment v)) → m (PLift (SegmentsAll p segments))
  | [] => pure ⟨True.intro⟩
  | segment :: rest => do
      let ⟨segmentProof⟩ ← segment.proveAll prove
      let ⟨restProof⟩ ← proveSegments prove rest
      pure ⟨⟨segmentProof, restProof⟩⟩

public def proveAll
    {m : Type → Type u₁}
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Prop}
    [Monad m]
    (prove : ∀ {a} (value : v a), m (PLift (p value)))
    (fragment : Fragment v) : m (PLift (fragment.All p)) :=
  proveSegments prove fragment.segments

@[expose] public def holeCount {v : ObjTy → Type} (fragment : Fragment v) : Nat :=
  fragment.segments.foldl (fun count segment => count + segment.holeCount) 0

private theorem mapSegmentsId {v : ObjTy → Type} (segments : List (Segment v)) :
    segments.map (Segment.map fun value => value) = segments := by
  induction segments with
  | nil => rfl
  | cons segment rest induction => simp [Segment.map_id, induction]

private theorem mapSegmentsComp {v : ObjTy → Type} {w x : ObjTy → Type}
    (left : ∀ {a}, v a → w a)
    (right : ∀ {a}, w a → x a)
    (segments : List (Segment v)) :
    (segments.map (Segment.map left)).map (Segment.map right) =
      segments.map (Segment.map fun value => right (left value)) := by
  induction segments with
  | nil => rfl
  | cons segment rest induction => simp [Segment.map_comp, induction]

@[simp] public theorem map_id {v : ObjTy → Type} (fragment : Fragment v) :
    fragment.map (fun value => value) = fragment := by
  cases fragment with
  | mk segments requirements => simp [map, mapSegmentsId]

public theorem map_comp {v : ObjTy → Type} {w x : ObjTy → Type}
    (left : ∀ {a}, v a → w a)
    (right : ∀ {a}, w a → x a)
    (fragment : Fragment v) :
    (fragment.map left).map right =
      fragment.map (fun value => right (left value)) := by
  cases fragment with
  | mk segments requirements =>
      simp only [map]
      rw [mapSegmentsComp]

end Fragment

/-- A fragment tagged with the open slot contract implemented by its source codec. -/
public structure EncodedArg (v : ObjTy → Type) (_key : SlotKey) where
  fragment : Fragment v

namespace EncodedArg

public def map {v w : ObjTy → Type} {key : SlotKey} (η : ∀ {a}, v a → w a)
    (argument : EncodedArg v key) : EncodedArg w key :=
  ⟨argument.fragment.map η⟩

/-- Transform every dynamic hole in one encoded argument from left to right. -/
public def traverseK
    {v w : ObjTy → Type}
    {key : SlotKey}
    {r : Type u₁}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (argument : EncodedArg v key)
    (next : EncodedArg w key → r) : r :=
  argument.fragment.traverseK visit fun fragment => next ⟨fragment⟩

public def All {v : ObjTy → Type} {key : SlotKey} (p : ∀ {a}, v a → Prop)
    (argument : EncodedArg v key) : Prop :=
  argument.fragment.All p

@[expose] public def AllT
    {v : ObjTy → Type} {key : SlotKey}
    (p : ∀ {a}, v a → Type u₂) (argument : EncodedArg v key) : Type u₂ :=
  argument.fragment.AllT p

@[expose] public def traverseKAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₂}
    {w : ObjTy → Type}
    {key : SlotKey}
    {r : Type u₁}
    (visit : ∀ {a} (value : v a), p value → (w a → r) → r)
    (argument : EncodedArg v key)
    (evidence : argument.AllT p)
    (next : EncodedArg w key → r) : r :=
  argument.fragment.traverseKAllT visit evidence fun fragment => next ⟨fragment⟩

@[expose] public def mapAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₁}
    {q : ∀ {a}, v a → Type u₂}
    {key : SlotKey}
    (transform : ∀ {a} (value : v a), p value → q value)
    (argument : EncodedArg v key) : argument.AllT p → argument.AllT q :=
  argument.fragment.mapAllT transform

public def proveAll
    {m : Type → Type u₁}
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Prop}
    {key : SlotKey}
    [Monad m]
    (prove : ∀ {a} (value : v a), m (PLift (p value)))
    (argument : EncodedArg v key) : m (PLift (argument.All p)) :=
  argument.fragment.proveAll prove

@[expose] public def requirements {v : ObjTy → Type} {key : SlotKey} (argument : EncodedArg v key) : ReqRow :=
  argument.fragment.requirements

@[simp] public theorem map_requirements {key : SlotKey} {v w : ObjTy → Type}
    (f : ∀ {a}, v a → w a) (argument : EncodedArg v key) :
    (argument.map f).requirements = argument.requirements := private_decl% (by rfl)

@[expose] public def holeCount {v : ObjTy → Type} {key : SlotKey} (argument : EncodedArg v key) : Nat :=
  argument.fragment.holeCount

@[simp] public theorem map_id {v : ObjTy → Type} {key : SlotKey} (argument : EncodedArg v key) :
    argument.map (fun value => value) = argument := by
  cases argument
  simp [map]

public theorem map_comp {v : ObjTy → Type} {key : SlotKey} {w x : ObjTy → Type}
    (left : ∀ {a}, v a → w a)
    (right : ∀ {a}, w a → x a)
    (argument : EncodedArg v key) :
    (argument.map left).map right = argument.map (fun value => right (left value)) := by
  cases argument
  simp [map, Fragment.map_comp]

end EncodedArg

/-- Heterogeneous encoded arguments indexed by a command argument schema. -/
public abbrev EncodedArgs (v : ObjTy → Type) (schema : List SlotKey) :=
  Args (EncodedArg v) schema

namespace EncodedArgs

@[expose] public def requirements {v : ObjTy → Type} {schema : List SlotKey} :
    EncodedArgs v schema → ReqRow
  | arguments => arguments.foldl (fun result argument => result ||| argument.requirements) Req.none

private theorem fold_requirements {v : ObjTy → Type} {schema : List SlotKey}
    (args : EncodedArgs v schema) (r : ReqRow) :
    args.foldl (fun r a => r ||| a.requirements) r = r ||| args.requirements := by
  induction args generalizing r with
  | nil => simp [Args.foldl, requirements, Req.none]
  | cons arg args ih =>
      change args.foldl _ (r ||| arg.requirements) =
        r ||| args.foldl _ (Req.none ||| arg.requirements)
      rw [ih, ih]
      simp [Req.none, BitVec.or_assoc]

@[simp] public theorem requirements_nil {v : ObjTy → Type} :
    requirements (Args.nil : EncodedArgs v []) = Req.none := rfl

@[simp] public theorem requirements_cons {v : ObjTy → Type} {key : SlotKey} {keys : List SlotKey}
    (arg : EncodedArg v key) (args : EncodedArgs v keys) :
    requirements (Args.cons arg args) = arg.requirements ||| args.requirements := by
  change args.foldl _ (Req.none ||| arg.requirements) = _
  rw [fold_requirements]
  simp [Req.none]

@[simp] public theorem requirements_map {schema : List SlotKey} {v w : ObjTy → Type}
    (f : ∀ {a}, v a → w a) (args : EncodedArgs v schema) :
    requirements (Args.map (g := EncodedArg w) (EncodedArg.map f) args) = args.requirements := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
      simp [Args.map, requirements_cons, EncodedArg.map, EncodedArg.requirements,
        Fragment.map, ih]

@[expose] public def holeCount {v : ObjTy → Type} {schema : List SlotKey} : EncodedArgs v schema → Nat
  | arguments => arguments.foldl (fun result argument => result + argument.holeCount) 0

@[simp] public theorem map_id {v : ObjTy → Type} {schema : List SlotKey}
    (arguments : EncodedArgs v schema) :
    arguments.map (EncodedArg.map fun value => value) = arguments := by
  induction arguments with
  | nil => rfl
  | cons argument rest induction => simp [Args.map, EncodedArg.map_id, induction]

public theorem map_comp {v : ObjTy → Type} {schema : List SlotKey} {w x : ObjTy → Type}
    (left : ∀ {a}, v a → w a)
    (right : ∀ {a}, w a → x a)
    (arguments : EncodedArgs v schema) :
    (arguments.map (EncodedArg.map left)).map (EncodedArg.map right) =
      arguments.map (EncodedArg.map fun value => right (left value)) := by
  induction arguments with
  | nil => rfl
  | cons argument rest induction =>
      simp [Args.map, EncodedArg.map_comp, induction]

end EncodedArgs

/-- One catalog-owned part of a command template. Slots are statically bounded by the schema. -/
public inductive TemplatePart (schema : List SlotKey) where
  | token : SyntaxToken → TemplatePart schema
  | space : TemplatePart schema
  | slot : Fin schema.length → TemplatePart schema
  deriving BEq, DecidableEq, Repr

/-- Fixed command syntax with typed positions for encoded arguments. -/
public structure Template (schema : List SlotKey) where
  parts : List (TemplatePart schema)
  deriving BEq, DecidableEq, Repr

namespace Template

/-- A fixed keyword prefix followed by every schema argument in order. -/
@[expose] public def positional {schema : List SlotKey} (keywords : List SyntaxToken) : Template schema :=
  ⟨((keywords.map (TemplatePart.token (schema := schema))) ++
    (List.finRange schema.length).map TemplatePart.slot).intersperse .space⟩

private def slotIndices {schema : List SlotKey} : List (TemplatePart schema) → List Nat
  | [] => []
  | .slot index :: rest => index.val :: slotIndices rest
  | _ :: rest => slotIndices rest

private def spacingValid {schema : List SlotKey} : List (TemplatePart schema) → Bool
  | [] => false
  | .space :: _ => false
  | _ :: rest => expectSpace rest
where
  expectSpace : List (TemplatePart schema) → Bool
    | [] => true
    | .space :: rest => expectPart rest
    | _ => false

  expectPart : List (TemplatePart schema) → Bool
    | [] => false
    | .space :: _ => false
    | _ :: rest => expectSpace rest

public def valid {schema : List SlotKey} (template : Template schema) : Bool :=
  let slots := slotIndices template.parts
  spacingValid template.parts && decide slots.Nodup && slots.length == schema.length

end Template

/-- Argument contracts and intrinsic requirements/effects of a native command. -/
public structure Signature where
  schema : List SlotKey
  req : ReqRow
  eff : EffRow
  deriving BEq, DecidableEq, Repr

namespace Signature

@[expose] public def grade (sig : Signature) : Grade :=
  { req := sig.req, eff := sig.eff ||| Eff.failure }

end Signature

/-- A named command declaration with its signature and argument template. -/
public structure Decl where
  key : Lean.Name
  sig : Signature
  template : Template sig.schema
  cost : Option Nat := none
  deriving DecidableEq

/-- A command reference whose signature and template are checked during linking. -/
public structure Ref (sig : Signature) where
  key : Lean.Name
  template : Template sig.schema
  /-- Upper bound on native execution cost, excluding compiler-generated stores and macros. -/
  cost : Option Nat := none
  deriving Repr

/-- One command call with encoded arguments and typed dynamic values. -/
public structure Call (v : ObjTy → Type) (sig : Signature) where
  ref : Ref sig
  args : EncodedArgs v sig.schema

namespace Ref

@[expose] public def signature {sig : Signature} (_ref : Ref sig) : Signature := sig

@[expose] public def declaration {sig : Signature} (ref : Ref sig) : Decl :=
  { key := ref.key, sig, template := ref.template, cost := ref.cost }

@[expose] public def call {sig : Signature} {v : ObjTy → Type} (ref : Ref sig) (args : EncodedArgs v sig.schema) :
    Call v sig :=
  { ref, args }

end Ref

namespace Call

@[expose] public def requirements {v : ObjTy → Type} {sig : Signature} (request : Call v sig) : ReqRow :=
  request.args.requirements

@[expose] public def grade {v : ObjTy → Type} {sig : Signature} (request : Call v sig) : Grade :=
  ⟨sig.req ||| request.requirements, sig.eff ||| Eff.failure⟩

public def map {v w : ObjTy → Type} {sig : Signature} (η : ∀ {a}, v a → w a)
    (request : Call v sig) : Call w sig :=
  { request with args := request.args.map (EncodedArg.map η) }

@[simp] public theorem map_requirements {sig : Signature} {v w : ObjTy → Type}
    (f : ∀ {a}, v a → w a) (request : Call v sig) :
    (request.map f).requirements = request.requirements := by
  simp [map, requirements]

@[simp] public theorem map_grade {sig : Signature} {v w : ObjTy → Type}
    (f : ∀ {a}, v a → w a) (request : Call v sig) :
    (request.map f).grade = request.grade := by simp [grade]

/-- Transform all dynamic holes in argument and fragment order. -/
public def traverseK
    {v w : ObjTy → Type}
    {sig : Signature}
    {r : Type u₁}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (request : Call v sig)
    (next : Call w sig → r) : r :=
  request.args.traverseK (EncodedArg.traverseK visit) fun args =>
    next { request with args }

public def All {v : ObjTy → Type} {sig : Signature} (p : ∀ {a}, v a → Prop)
    (request : Call v sig) : Prop :=
  request.args.All (EncodedArg.All p)

@[expose] public def AllT
    {v : ObjTy → Type} {sig : Signature}
    (p : ∀ {a}, v a → Type u₂) (request : Call v sig) :=
  request.args.AllT (EncodedArg.AllT p)

@[expose] public def traverseKAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₂}
    {w : ObjTy → Type}
    {sig : Signature}
    {r : Type u₁}
    (visit : ∀ {a} (value : v a), p value → (w a → r) → r)
    (request : Call v sig)
    (evidence : request.AllT p)
    (next : Call w sig → r) : r := by
  change request.args.AllT (EncodedArg.AllT p) at evidence
  exact request.args.traverseKAllT
    (fun argument proof next => argument.traverseKAllT visit proof next)
    evidence fun args => next { request with args }

@[expose] public def mapAllT
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Type u₁}
    {q : ∀ {a}, v a → Type u₂}
    {sig : Signature}
    (transform : ∀ {a} (value : v a), p value → q value)
    (request : Call v sig) : request.AllT p → request.AllT q := by
  change request.args.AllT (EncodedArg.AllT p) →
    request.args.AllT (EncodedArg.AllT q)
  exact Args.AllT.map
    (fun argument proof => argument.mapAllT transform proof)
    request.args

public def proveAll
    {m : Type → Type u₁}
    {v : ObjTy → Type}
    {p : ∀ {a}, v a → Prop}
    {sig : Signature}
    [Monad m]
    (prove : ∀ {a} (value : v a), m (PLift (p value)))
    (request : Call v sig) : m (PLift (request.All p)) :=
  request.args.proveAll (EncodedArg.proveAll prove)

@[expose] public def holeCount {v : ObjTy → Type} {sig : Signature} (request : Call v sig) : Nat :=
  request.args.holeCount

@[simp] public theorem map_id {v : ObjTy → Type} {sig : Signature} (request : Call v sig) :
    request.map (fun value => value) = request := by
  cases request
  simp [map]

public theorem map_comp {v : ObjTy → Type} {sig : Signature} {w x : ObjTy → Type}
    (left : ∀ {a}, v a → w a)
    (right : ∀ {a}, w a → x a)
    (request : Call v sig) :
    (request.map left).map right = request.map (fun value => right (left value)) := by
  cases request
  simp [map, EncodedArgs.map_comp]

end Call

end Oria.Command
