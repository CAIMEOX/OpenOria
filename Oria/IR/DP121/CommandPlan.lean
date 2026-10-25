module

public import Oria.Command.Catalog
public import Oria.Nbt.Basic

namespace Oria.Target.DP121

universe u

open Oria.Command

/-- Target-owned computational evidence for one exact typed resolved reference. -/
public structure ResolvedCommand (sig : Command.Signature) where
  ref : Command.Ref sig
  catalog : Catalog
  resolved : Catalog.ResolvedRef catalog ref

public structure MacroParameter (_a : ObjTy) where
  index : Nat
  deriving BEq, DecidableEq, Repr

public structure HolePlan (v : ObjTy → Type) (a : ObjTy) where
  codec : HoleCodec a
  source : v a
  parameter : MacroParameter a

public inductive CommandPiece (v : ObjTy → Type) where
  | token : SyntaxToken → CommandPiece v
  | space : CommandPiece v
  | i32 : Int32 → CommandPiece v
  | literal : Literal → CommandPiece v
  | hole {a : ObjTy} : HolePlan v a → CommandPiece v

namespace CommandPiece

public def mapK {v w : ObjTy → Type} (η : ∀ {a}, v a → w a) : CommandPiece v → CommandPiece w
  | CommandPiece.token value => @CommandPiece.token w value
  | CommandPiece.space => @CommandPiece.space w
  | CommandPiece.i32 value => @CommandPiece.i32 w value
  | CommandPiece.literal value => @CommandPiece.literal w value
  | CommandPiece.hole h => @CommandPiece.hole w _ { h with source := η h.source }

public def traverseK {v w : ObjTy → Type} {r : Type u}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (piece : CommandPiece v) (next : CommandPiece w → r) : r :=
  match piece with
  | CommandPiece.token value => next (@CommandPiece.token w value)
  | CommandPiece.space => next (@CommandPiece.space w)
  | CommandPiece.i32 value => next (@CommandPiece.i32 w value)
  | CommandPiece.literal value => next (@CommandPiece.literal w value)
  | CommandPiece.hole h => visit h.source fun source =>
      next (@CommandPiece.hole w _ { h with source })

@[simp] public theorem mapK_id {v : ObjTy → Type} (piece : CommandPiece v) :
    piece.mapK (fun value => value) = piece := by
  cases piece <;> simp [mapK]

public theorem mapK_comp {v : ObjTy → Type} {w x : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (θ : ∀ {a}, w a → x a)
    (piece : CommandPiece v) :
    (piece.mapK η).mapK θ = piece.mapK (fun value => θ (η value)) := by
  cases piece <;> simp [mapK]

end CommandPiece

/-- Source-independent command shape used to state traversal preservation. -/
public inductive PieceShape where
  | token : SyntaxToken → PieceShape
  | space : PieceShape
  | i32 : Int32 → PieceShape
  | literal : String → PieceShape
  | hole : Nat → PieceShape
  deriving BEq, DecidableEq, Repr

@[expose] public def CommandPiece.shape {v : ObjTy → Type} : CommandPiece v → PieceShape
  | .token value => .token value
  | .space => .space
  | .i32 value => .i32 value
  | .literal value => .literal (value.format.pretty 120)
  | .hole h => .hole h.parameter.index

@[simp] private theorem CommandPiece.shape_mapK {v w : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (piece : CommandPiece v) :
    (piece.mapK η).shape = piece.shape := by
  cases piece <;> rfl

/-- One target macro field with its exact object type and serialization evidence. -/
public structure MacroField where
  ty : ObjTy
  codec : HoleCodec ty
  deriving DecidableEq

/-- The ordered field contract read from one function-macro source compound. -/
public structure MacroSchema where
  private mk ::
  fields : List MacroField
  deriving DecidableEq

namespace MacroSchema

@[expose] public def ofFields (fields : List MacroField) : MacroSchema :=
  private_decl% ⟨fields⟩

@[simp] public theorem fields_ofFields (fields : List MacroField) :
    (ofFields fields).fields = fields :=
  private_decl% (by rfl)

/-- The canonical storage key and function-macro name for one schema position. -/
@[expose] public def parameterKey
    (schema : MacroSchema)
    (position : Fin schema.fields.length) : Nbt.Key :=
  ⟨"p" ++ toString position.val⟩

end MacroSchema

/-- Whether a target command line is static or scoped by one macro schema. -/
public inductive Mode where
  | plain
  | macro (schema : MacroSchema)

/-- A command fragment whose dynamic parameters are bounded by its macro schema. -/
public inductive Piece : Mode → Type where
  | token {mode} : SyntaxToken → Piece mode
  | space {mode} : Piece mode
  | i32 {mode} : Int32 → Piece mode
  | literal {mode} : Literal → Piece mode
  | parameter {schema : MacroSchema} (position : Fin schema.fields.length) : Piece (.macro schema)

namespace Piece

@[expose] public def parameterCount {mode : Mode} : Piece mode → Nat
  | .token _ | .space | .i32 _ | .literal _ => 0
  | .parameter _ => 1

private def plainCommandPiece {v : ObjTy → Type} : Piece .plain → CommandPiece v
  | .token value => .token value
  | .space => .space
  | .i32 value => .i32 value
  | .literal value => .literal value

end Piece

/-- Sources indexed by the exact ordered field contract of a macro invocation. -/
public abbrev InvocationSources (v : ObjTy → Type) (schema : MacroSchema) :=
  Args (fun field : MacroField => v field.ty) schema.fields

namespace Piece

private def macroCommandPiece {v : ObjTy → Type} {schema : MacroSchema}
    (sources : InvocationSources v schema) :
    Piece (.macro schema) → CommandPiece v
  | .token value => .token value
  | .space => .space
  | .i32 value => .i32 value
  | .literal value => .literal value
  | .parameter position => .hole {
      codec := (schema.fields.get position).codec
      source := sources.get position
      parameter := ⟨position.val⟩
    }

@[simp] private theorem plainCommandPiece_mapK {v w : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (piece : Piece .plain) :
    (piece.plainCommandPiece : CommandPiece v).mapK η =
      (piece.plainCommandPiece : CommandPiece w) := by
  cases piece <;> rfl

@[simp] private theorem macroCommandPiece_mapK {v w : ObjTy → Type} {schema : MacroSchema}
    (η : ∀ {a}, v a → w a)
    (sources : InvocationSources v schema)
    (piece : Piece (.macro schema)) :
    (piece.macroCommandPiece (sources.map fun value => η value)) =
      (piece.macroCommandPiece sources).mapK η := by
  cases piece <;> simp [macroCommandPiece, CommandPiece.mapK]

end Piece

/-- One resolved command with pieces scoped by its macro schema. -/
public structure Invocation (mode : Mode) (sig : Command.Signature) where
  private mk ::
  resolved : ResolvedCommand sig
  pieces : Array (Piece mode)

private def pieceParameterCount {mode : Mode} (pieces : List (Piece mode)) : Nat :=
  (pieces.map Piece.parameterCount).sum

@[simp] private theorem pieceParameterCount_nil {mode : Mode} :
    pieceParameterCount ([] : List (Piece mode)) = 0 := rfl

@[simp] private theorem pieceParameterCount_cons {mode : Mode}
    (piece : Piece mode) (rest : List (Piece mode)) :
    pieceParameterCount (piece :: rest) =
      piece.parameterCount + pieceParameterCount rest := by
  simp [pieceParameterCount]

namespace Invocation

@[expose] public def parameterCount {mode : Mode} {sig : Command.Signature}
    (invocation : Invocation mode sig) : Nat :=
  private_decl% pieceParameterCount invocation.pieces.toList

end Invocation

/-- Effect of a compiler-owned native fragment on scalar registers, call-frame words,
and the macro argument compound. Other world and owned-document state is independent. -/
public inductive TemporaryEffect where
  | preserves
  | unknown
  deriving BEq, DecidableEq

/-- A planned fragment invocation has no catalog-owned command identity. -/
public structure FragmentInvocation (mode : Mode) where
  private mk ::
  pieces : Array (Piece mode)
  /-- Optional native cost supplied by compiler-owned fragment construction. -/
  cost : Option Nat := none
  temporaries : TemporaryEffect := .unknown

namespace FragmentInvocation

private def staticPiece {mode : Mode} : Segment (fun _ => Empty) → Piece mode
  | .token value => .token value
  | .space => .space
  | .i32 value => .i32 value
  | .literal value => .literal value
  | .hole _ impossible => nomatch impossible

/-- Add static command syntax around a selection while retaining its macro scope. -/
@[expose] public def surround {mode : Mode} (value : FragmentInvocation mode)
    (before after : Fragment (fun _ => Empty)) : FragmentInvocation mode :=
  private_decl% { value with temporaries := .unknown, pieces :=
    (before.segments.map staticPiece).toArray ++ value.pieces ++
      (after.segments.map staticPiece).toArray }

@[expose] public def withCost {mode : Mode} (value : FragmentInvocation mode) (cost : Nat) :
    FragmentInvocation mode := private_decl% { value with cost := some cost }

/-- Record the temporary-state contract at the native operation's lowering site. -/
@[expose] public def withTemporaries {mode : Mode} (value : FragmentInvocation mode)
    (effect : TemporaryEffect) : FragmentInvocation mode :=
  private_decl% {value with temporaries := effect}

@[expose] public def parameterCount {mode : Mode} (invocation : FragmentInvocation mode) : Nat :=
  private_decl% pieceParameterCount invocation.pieces.toList

@[simp] public theorem parameterCount_withCost {mode : Mode} (value : FragmentInvocation mode) (cost : Nat) :
    (value.withCost cost).parameterCount = value.parameterCount := private_decl% rfl

@[simp] public theorem parameterCount_withTemporaries {mode : Mode} (value : FragmentInvocation mode)
    (effect : TemporaryEffect) : (value.withTemporaries effect).parameterCount = value.parameterCount :=
  private_decl% rfl

@[simp] public theorem parameterCount_surround {mode : Mode} (value : FragmentInvocation mode)
    (before after : Fragment (fun _ => Empty)) :
    (value.surround before after).parameterCount = value.parameterCount := private_decl% (by
  have zero (segments : List (Segment (fun _ => Empty))) :
      ((segments.map (staticPiece (mode := mode))).map Piece.parameterCount).sum = 0 := by
    induction segments with
    | nil => rfl
    | cons head tail ih =>
      cases head <;> simp_all [staticPiece, Piece.parameterCount]
      rename_i impossible
      exact nomatch impossible
  change (((before.segments.map staticPiece).toArray ++ value.pieces ++
    (after.segments.map staticPiece).toArray).toList.map Piece.parameterCount).sum =
      (value.pieces.toList.map Piece.parameterCount).sum
  simp only [Array.toList_append, List.map_append, List.sum_append,
    zero, Nat.zero_add, Nat.add_zero])

end FragmentInvocation

private inductive CommandPlanCore (v : ObjTy → Type) (sig : Command.Signature) where
  | plain (resolved : ResolvedCommand sig) (pieces : Array (Piece .plain))
  | macro
      (resolved : ResolvedCommand sig)
      (fields : List MacroField)
      (nonempty : 0 < fields.length)
      (sources : InvocationSources v (.ofFields fields))
      (pieces : Array (Piece (.macro (.ofFields fields))))
      (complete : pieceParameterCount pieces.toList = fields.length)

public structure CommandPlan (v : ObjTy → Type) (sig : Command.Signature) where
  private mk ::
  private core : CommandPlanCore v sig
  requirements : ReqRow

namespace CommandPlan

private def resolvedImpl {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) : ResolvedCommand sig :=
  match plan with
  | ⟨.plain resolved _, _⟩ | ⟨.macro resolved _ _ _ _ _, _⟩ => resolved

@[expose] public def resolved {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) : ResolvedCommand sig :=
  private_decl% resolvedImpl plan

private def piecesImpl {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) : Array (CommandPiece v) :=
  match plan with
  | ⟨.plain _ pieces, _⟩ => pieces.map Piece.plainCommandPiece
  | ⟨.macro _ _ _ sources pieces _, _⟩ =>
      pieces.map (Piece.macroCommandPiece sources)

@[expose] public def pieces {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) : Array (CommandPiece v) :=
  private_decl% piecesImpl plan

@[simp] private theorem resolved_plain {sig : Command.Signature} {v : ObjTy → Type}
    (resolved : ResolvedCommand sig) (pieces : Array (Piece .plain))
    (requirements : ReqRow) :
    (⟨.plain resolved pieces, requirements⟩ : CommandPlan v sig).resolved =
      resolved :=
  private_decl% (by rfl)

@[simp] private theorem resolved_macro {sig : Command.Signature} {v : ObjTy → Type}
    (resolved : ResolvedCommand sig) (fields : List MacroField)
    (nonempty : 0 < fields.length)
    (sources : InvocationSources v (.ofFields fields))
    (pieces : Array (Piece (.macro (.ofFields fields))))
    (complete : pieceParameterCount pieces.toList = fields.length)
    (requirements : ReqRow) :
    (⟨.macro resolved fields nonempty sources pieces complete,
      requirements⟩ : CommandPlan v sig).resolved = resolved :=
  private_decl% (by rfl)

@[simp] private theorem pieces_plain {sig : Command.Signature} {v : ObjTy → Type}
    (resolved : ResolvedCommand sig) (pieces : Array (Piece .plain))
    (requirements : ReqRow) :
    (⟨.plain resolved pieces, requirements⟩ : CommandPlan v sig).pieces =
      pieces.map Piece.plainCommandPiece :=
  private_decl% (by rfl)

@[simp] private theorem pieces_macro {sig : Command.Signature} {v : ObjTy → Type}
    (resolved : ResolvedCommand sig) (fields : List MacroField)
    (nonempty : 0 < fields.length)
    (sources : InvocationSources v (.ofFields fields))
    (pieces : Array (Piece (.macro (.ofFields fields))))
    (complete : pieceParameterCount pieces.toList = fields.length)
    (requirements : ReqRow) :
    (⟨.macro resolved fields nonempty sources pieces complete,
      requirements⟩ : CommandPlan v sig).pieces =
      pieces.map (Piece.macroCommandPiece sources) :=
  private_decl% (by rfl)

public def mapK {v w : ObjTy → Type} {sig : Command.Signature}
    (η : ∀ {a}, v a → w a) (plan : CommandPlan v sig) :
    CommandPlan w sig :=
  match plan with
  | ⟨.macro resolved fields nonempty sources pieces complete, requirements⟩ =>
      ⟨.macro resolved fields nonempty (sources.map fun value => η value) pieces complete,
        requirements⟩
  | ⟨.plain resolved pieces, requirements⟩ =>
      ⟨.plain resolved pieces, requirements⟩

@[simp] public theorem resolved_mapK {v : ObjTy → Type} {sig : Command.Signature} {w : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (plan : CommandPlan v sig) :
    (plan.mapK η).resolved = plan.resolved :=
  private_decl% (by
    rcases plan with ⟨core, _⟩
    cases core <;> rfl)

@[simp] public theorem pieces_mapK {v : ObjTy → Type} {sig : Command.Signature} {w : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (plan : CommandPlan v sig) :
    (plan.mapK η).pieces = plan.pieces.map (CommandPiece.mapK η) :=
  private_decl% (by
    rcases plan with ⟨core, _⟩
    cases core <;> simp [mapK, Array.map_map])

@[simp] public theorem requirements_mapK {v : ObjTy → Type} {sig : Command.Signature} {w : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (plan : CommandPlan v sig) :
    (plan.mapK η).requirements = plan.requirements :=
  private_decl% (by
    rcases plan with ⟨core, _⟩
    cases core <;> rfl)

@[expose] public def shapes {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) : Array PieceShape :=
  plan.pieces.map CommandPiece.shape

@[simp] public theorem shapes_mapK {v : ObjTy → Type} {sig : Command.Signature} {w : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (plan : CommandPlan v sig) :
    (plan.mapK η).shapes = plan.shapes := by
  simp only [shapes]
  rw [pieces_mapK]
  simp [Array.map_map, CommandPiece.shape_mapK]

public def traverseK {v w : ObjTy → Type} {sig : Command.Signature} {r : Type u}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (plan : CommandPlan v sig) (next : CommandPlan w sig → r) : r :=
  match plan with
  | ⟨.macro resolved fields nonempty sources pieces complete, requirements⟩ =>
      sources.traverseK
        (fun {field} value k => visit (a := field.ty) value k) fun transformed =>
        next ⟨.macro resolved fields nonempty transformed pieces complete,
          requirements⟩
  | ⟨.plain resolved pieces, requirements⟩ =>
      next ⟨.plain resolved pieces, requirements⟩

public theorem traverseK_pure {v w : ObjTy → Type} {sig : Command.Signature} {r : Type u}
    (η : ∀ {a}, v a → w a) (plan : CommandPlan v sig)
    (next : CommandPlan w sig → r) :
    plan.traverseK (fun value k => k (η value)) next =
      next (plan.mapK η) :=
  private_decl% (by
    rcases plan with ⟨core, _⟩
    cases core <;> simp [traverseK, mapK, Args.traverseK_pure])

@[simp] public theorem mapK_id {v : ObjTy → Type} {sig : Command.Signature} (plan : CommandPlan v sig) :
    plan.mapK (fun value => value) = plan :=
  private_decl% (by
    rcases plan with ⟨core, _⟩
    cases core <;> simp [mapK])

public theorem mapK_comp {v : ObjTy → Type} {sig : Command.Signature} {w x : ObjTy → Type}
    (η : ∀ {a}, v a → w a) (θ : ∀ {a}, w a → x a)
    (plan : CommandPlan v sig) :
    (plan.mapK η).mapK θ = plan.mapK (fun value => θ (η value)) :=
  private_decl% (by
    rcases plan with ⟨core, _⟩
    cases core <;> simp [mapK, Args.map_comp])

/-- Expose a resolved invocation with its typed macro sources and parameter count. -/
public def withInvocation {v : ObjTy → Type} {sig : Command.Signature} {r : Type u}
    (plan : CommandPlan v sig)
    (plain : Invocation .plain sig → r)
    (onMacro : (schema : MacroSchema) →
      0 < schema.fields.length →
      InvocationSources v schema →
      (invocation : Invocation (.macro schema) sig) →
      invocation.parameterCount = schema.fields.length → r) : r :=
  match plan with
  | ⟨.plain resolved pieces, _⟩ => plain ⟨resolved, pieces⟩
  | ⟨.macro resolved fields nonempty sources pieces complete, _⟩ =>
      onMacro (.ofFields fields) nonempty sources ⟨resolved, pieces⟩ complete

/-- Plain invocations have no parameters; macro invocations cover their schema exactly. -/
public theorem withInvocation_coverage {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) :
    plan.withInvocation
      (fun invocation => invocation.parameterCount = 0)
      (fun schema _nonempty _sources invocation _complete =>
        invocation.parameterCount = schema.fields.length) :=
  private_decl% (by
    rcases plan with ⟨core, requirements⟩
    cases core
    · rename_i resolved pieces
      simp only [withInvocation]
      change pieceParameterCount pieces.toList = 0
      induction pieces.toList with
      | nil => rfl
      | cons piece rest induction =>
          cases piece <;>
            simp [Piece.parameterCount, induction]
    · rename_i resolved fields nonempty sources pieces complete
      simp only [withInvocation]
      exact complete)

public theorem withInvocation_certified {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) :
    plan.withInvocation
      (fun invocation =>
        invocation.resolved = plan.resolved ∧ invocation.parameterCount = 0)
      (fun schema _nonempty _sources invocation _complete =>
        invocation.resolved = plan.resolved ∧
          invocation.parameterCount = schema.fields.length ∧
          0 < invocation.parameterCount) :=
  private_decl% (by
    rcases plan with ⟨core, requirements⟩
    cases core
    · rename_i resolved pieces
      simp only [withInvocation]
      refine ⟨rfl, ?_⟩
      change pieceParameterCount pieces.toList = 0
      induction pieces.toList with
      | nil => rfl
      | cons piece rest induction =>
          cases piece <;>
            simp [Piece.parameterCount, induction]
    · rename_i resolved fields nonempty sources pieces complete
      simp only [withInvocation]
      refine ⟨rfl, ?_, ?_⟩
      · exact complete
      · change 0 < pieceParameterCount pieces.toList
        rw [complete]
        exact nonempty)

end CommandPlan


/-- Number of dynamic fields represented by a raw segment stream. -/
private def segmentParameterCount {v : ObjTy → Type} (segments : List (Segment v)) : Nat :=
  (segments.map Segment.holeCount).sum

/-- The schema and typed sources collected without assigning bounded positions yet. -/
private structure InvocationSchema
    (v : ObjTy → Type) (segments : List (Segment v)) where
  fields : List MacroField
  sources : InvocationSources v (.ofFields fields)
  complete : fields.length = segmentParameterCount segments

private def collectInvocationSchema {v : ObjTy → Type} :
    (segments : List (Segment v)) → InvocationSchema v segments
  | [] => ⟨[], .nil, rfl⟩
  | .token _ :: rest =>
      let collected := collectInvocationSchema rest
      ⟨collected.fields, collected.sources, by
        simpa [segmentParameterCount, Segment.holeCount] using collected.complete⟩
  | .space :: rest =>
      let collected := collectInvocationSchema rest
      ⟨collected.fields, collected.sources, by
        simpa [segmentParameterCount, Segment.holeCount] using collected.complete⟩
  | .i32 _ :: rest =>
      let collected := collectInvocationSchema rest
      ⟨collected.fields, collected.sources, by
        simpa [segmentParameterCount, Segment.holeCount] using collected.complete⟩
  | .literal _ :: rest =>
      let collected := collectInvocationSchema rest
      ⟨collected.fields, collected.sources, by
        simpa [segmentParameterCount, Segment.holeCount] using collected.complete⟩
  | .hole codec source :: rest =>
      let collected := collectInvocationSchema rest
      let field : MacroField := ⟨_, codec⟩
      ⟨field :: collected.fields, .cons source collected.sources, by
        simp [segmentParameterCount, Segment.holeCount, collected.complete,
          Nat.add_comm]⟩

/-- Convert a certified static raw stream to its plain invocation pieces. -/
private def plainPieces {v : ObjTy → Type} :
    (segments : List (Segment v)) →
      segmentParameterCount segments = 0 → List (Piece .plain)
  | [], _ => []
  | .token value :: rest, complete =>
      .token value :: plainPieces rest (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .space :: rest, complete =>
      .space :: plainPieces rest (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .i32 value :: rest, complete =>
      .i32 value :: plainPieces rest (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .literal value :: rest, complete =>
      .literal value :: plainPieces rest (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .hole _ _ :: rest, complete => by
      simp [segmentParameterCount, Segment.holeCount] at complete

/-- Assign each raw hole its dense position after the complete schema is known. -/
private def macroPieces {v : ObjTy → Type} (allFields : List MacroField) :
    (segments : List (Segment v)) →
      (position : Nat) →
      position + segmentParameterCount segments = allFields.length →
      List (Piece (.macro (.ofFields allFields)))
  | [], _, _ => []
  | .token value :: rest, position, complete =>
      .token value :: macroPieces allFields rest position (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .space :: rest, position, complete =>
      .space :: macroPieces allFields rest position (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .i32 value :: rest, position, complete =>
      .i32 value :: macroPieces allFields rest position (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .literal value :: rest, position, complete =>
      .literal value :: macroPieces allFields rest position (by
        simpa [segmentParameterCount, Segment.holeCount] using complete)
  | .hole _ _ :: rest, position, complete =>
      .parameter ⟨position, by
        simp only [MacroSchema.fields_ofFields]
        simp [segmentParameterCount, Segment.holeCount] at complete
        omega⟩ ::
      macroPieces allFields rest (position + 1) (by
        simp [segmentParameterCount, Segment.holeCount] at complete ⊢
        omega)

private theorem pieceParameterCount_macroPieces {v : ObjTy → Type} {fields : List MacroField}
    (segments : List (Segment v))
    (position : Nat)
    (complete : position + segmentParameterCount segments = fields.length) :
    pieceParameterCount (macroPieces fields segments position complete) =
      segmentParameterCount segments := by
  induction segments generalizing position with
  | nil => rfl
  | cons segment rest induction =>
      cases segment <;>
        simp [macroPieces, Piece.parameterCount,
          segmentParameterCount, Segment.holeCount, induction]

private inductive InvocationBuild (v : ObjTy → Type) where
  | plain (pieces : List (Piece .plain))
  | macro
      (fields : List MacroField)
      (nonempty : 0 < fields.length)
      (sources : InvocationSources v (.ofFields fields))
      (pieces : List (Piece (.macro (.ofFields fields))))
      (complete : pieceParameterCount pieces = fields.length)

/-- A command fragment planned without resolving a catalog-owned command. -/
public structure FragmentPlan (v : ObjTy → Type) where
  private mk ::
  private core : InvocationBuild v
  requirements : ReqRow

namespace FragmentPlan

/-- Expose the planned fragment as a plain or macro invocation. -/
public def withInvocation {v : ObjTy → Type} {r : Type u}
    (plan : FragmentPlan v)
    (plain : FragmentInvocation .plain → r)
    (onMacro : (schema : MacroSchema) →
      0 < schema.fields.length →
      InvocationSources v schema →
      (invocation : FragmentInvocation (.macro schema)) →
      invocation.parameterCount = schema.fields.length → r) : r :=
  match plan with
  | ⟨.plain pieces, _⟩ => plain ⟨pieces.toArray, none, .unknown⟩
  | ⟨.macro fields nonempty sources pieces complete, _⟩ =>
      let schema := MacroSchema.ofFields fields
      let invocation : FragmentInvocation (.macro schema) := ⟨pieces.toArray, none, .unknown⟩
      onMacro schema nonempty sources invocation (by
        change pieceParameterCount pieces.toArray.toList = fields.length
        simpa using complete)

/-- Planned fragments have no parameters when plain and cover every macro field. -/
public theorem withInvocation_coverage {v : ObjTy → Type} (plan : FragmentPlan v) :
    plan.withInvocation
      (fun invocation => invocation.parameterCount = 0)
      (fun schema _nonempty _sources invocation _complete =>
        invocation.parameterCount = schema.fields.length) := by
  rcases plan with ⟨core, requirements⟩
  cases core with
  | plain pieces =>
      simp only [withInvocation]
      change pieceParameterCount pieces = 0
      induction pieces with
      | nil => rfl
      | cons piece rest induction =>
          cases piece <;> simpa [pieceParameterCount, Piece.parameterCount] using induction
  | «macro» fields nonempty sources pieces complete =>
      simp only [withInvocation]
      change pieceParameterCount pieces.toArray.toList = fields.length
      simpa using complete

/-- Macro fragment invocations are nonempty and cover their complete schema. -/
public theorem withInvocation_certified {v : ObjTy → Type} (plan : FragmentPlan v) :
    plan.withInvocation
      (fun invocation => invocation.parameterCount = 0)
      (fun schema _nonempty _sources invocation _complete =>
        invocation.parameterCount = schema.fields.length ∧
          0 < invocation.parameterCount) := by
  rcases plan with ⟨core, requirements⟩
  cases core with
  | plain pieces =>
      simp only [withInvocation]
      change pieceParameterCount pieces = 0
      induction pieces with
      | nil => rfl
      | cons piece rest induction =>
          cases piece <;> simpa [pieceParameterCount, Piece.parameterCount] using induction
  | «macro» fields nonempty sources pieces complete =>
      simp only [withInvocation]
      change pieceParameterCount pieces.toArray.toList = fields.length ∧
        0 < pieceParameterCount pieces.toArray.toList
      constructor
      · simpa using complete
      · rw [show pieceParameterCount pieces.toArray.toList = fields.length by simpa using complete]
        exact nonempty

end FragmentPlan

private def buildInvocation {v : ObjTy → Type} : List (Segment v) → InvocationBuild v
  | segments =>
      match collectInvocationSchema segments with
      | ⟨[], .nil, complete⟩ =>
          .plain (plainPieces segments complete.symm)
      | ⟨field :: fields, .cons source sources, complete⟩ =>
          let allFields := field :: fields
          let pieces := macroPieces allFields segments 0 (by
            simpa [allFields] using complete.symm)
          .macro allFields (by simp [allFields]) (.cons source sources) pieces (by
            rw [pieceParameterCount_macroPieces]
            exact complete.symm)

private def expandPart {v : ObjTy → Type} {schema : List SlotKey} (args : EncodedArgs v schema) :
    TemplatePart schema → List (Segment v)
  | .token token => [.token token]
  | .space => [.space]
  | .slot index => (args.get index).fragment.segments

private def expand {v : ObjTy → Type} {sig : Command.Signature}
    (request : Call v sig) : List (Segment v) :=
  request.ref.template.parts.flatMap (expandPart request.args)

private def planFragmentCore {v : ObjTy → Type} (fragment : Fragment v) :
    Except Diagnostic (InvocationBuild v) := do
  for segment in fragment.segments do
    match segment with
    | .literal value => value.check
    | _ => pure ()
  pure (buildInvocation fragment.segments)

/-- Plan a fragment's dense macro schema without requiring a catalog declaration. -/
public def planFragment {v : ObjTy → Type} (fragment : Fragment v) :
    Except Diagnostic (FragmentPlan v) := do
  pure ⟨← planFragmentCore fragment, fragment.requirements⟩

public def planWithCatalog {v : ObjTy → Type} {sig : Command.Signature}
    (catalog : Catalog) (request : Call v sig) :
    Except Diagnostic (CommandPlan v sig) := do
  let resolved ← catalog.resolveRef request.ref
  let resolved : ResolvedCommand sig := ⟨request.ref, catalog, resolved⟩
  let segments := expand request
  let fragment ← planFragment ⟨segments, request.requirements⟩
  match fragment with
  | ⟨.plain pieces, requirements⟩ =>
      pure ⟨.plain resolved pieces.toArray,
        requirements⟩
  | ⟨.macro fields nonempty sources pieces complete, requirements⟩ =>
      have canonical :
          pieceParameterCount pieces.toArray.toList = fields.length := by
        simpa using complete
      pure ⟨.macro resolved fields nonempty sources pieces.toArray canonical,
        requirements⟩

end Oria.Target.DP121
