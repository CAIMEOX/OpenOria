module

public import Oria.Nbt.Description
public import Oria.IR.Common.Scope

namespace Oria.IR.Nbt

/-- Whether native selection existence must be checked at this operation. -/
public inductive Check where
  | required
  | available
  deriving BEq, DecidableEq, Repr

/-- An owned-document selection, retained from typed access construction through target lowering.
`available` records presence established by a dominating successful operation. -/
public structure Path (i : Type) where
  segments : List (Oria.Nbt.PathSegment i)
  schema : Oria.Nbt.Schema
  check : Check

/-- Native selections start with required checks. Memory analysis may establish their
presence within a scope that contains no interfering native mutations. -/
@[expose] public def Path.ofSegments {i : Type} (schema : Oria.Nbt.Schema)
    (segments : List (Oria.Nbt.PathSegment i)) : Path i :=
  ⟨segments, schema, .required⟩

@[expose] public def Path.map {i j : Type} (f : i → j) (path : Path i) : Path j :=
  ⟨path.segments.map (·.map f), path.schema, path.check⟩

@[simp] public theorem Path.map_id {i : Type} (path : Path i) : path.map id = path := by
  cases path
  simp [map]

@[simp] public theorem Path.map_comp {i j k : Type} (f : i → j) (g : j → k) (path : Path i) :
    (path.map f).map g = path.map (g ∘ f) := by
  simp only [map, List.map_map, Function.comp_def, Oria.Nbt.PathSegment.map_comp]

/-- A native write retains its static NBT value or scalar operand until target encoding. -/
public inductive Write (i : Type) where
  | literal : Oria.Nbt.Any → Write i
  | i32 : i → Write i

@[expose] public def Write.map {i j : Type} (f : i → j) : Write i → Write j
  | .literal value => .literal value
  | .i32 value => .i32 (f value)

/-- Capture path indices in the operation's typed operand telescope. -/
public def abstractPath {v : ObjTy → Type} (path : Path (v .i32)) :
    (as : List ObjTy) × Path (Scope.Var Unit as .i32) × Args v as :=
  let ⟨as, segments, values⟩ := go path.segments
  ⟨as, ⟨segments, path.schema, path.check⟩, values⟩
where
  go : List (Oria.Nbt.PathSegment (v .i32)) →
      (as : List ObjTy) × List (Oria.Nbt.PathSegment (Scope.Var Unit as .i32)) × Args v as
    | [] => ⟨[], [], .nil⟩
    | .key key :: rest => let ⟨as, rest, values⟩ := go rest; ⟨as, .key key :: rest, values⟩
    | .all :: rest => let ⟨as, rest, values⟩ := go rest; ⟨as, .all :: rest, values⟩
    | .matching impossible :: _ => nomatch impossible
    | .index value :: rest =>
        let ⟨as, rest, values⟩ := go rest
        ⟨.i32 :: as, .index .head :: rest.map (·.map (fun x => x.weaken .i32)),
          .cons value values⟩

private theorem abstractSegments_restore {v : ObjTy → Type}
    (segments : List (Oria.Nbt.PathSegment (v .i32))) :
    let ⟨_, body, values⟩ := abstractPath.go segments
    body.map (·.map (fun x => x.lookup values)) = segments := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
      cases segment with
      | matching impossible => nomatch impossible
      | key key | all | index value =>
          simp only [abstractPath.go]
          generalize eq : abstractPath.go rest = out at *
          obtain ⟨as, body, values⟩ := out
          dsimp only at ih ⊢
          simp only [List.map_cons]
          congr 1 <;> first
          | (simp only [Oria.Nbt.PathSegment.map, Scope.Var.lookup_head]; done)
          | simpa only [List.map_map, Function.comp_def, Oria.Nbt.PathSegment.map_comp,
              Scope.Var.lookup_weaken] using ih

/-- Restoring the captured operands preserves the complete semantic selection. -/
public theorem abstractPath_restore {v : ObjTy → Type} (path : Path (v .i32)) :
    let ⟨_, body, values⟩ := abstractPath path
    body.map (fun x => x.lookup values) = path := by
  cases path with
  | mk segments schema check =>
      have h := abstractSegments_restore segments
      simp only [abstractPath, Path.map]
      generalize eq : abstractPath.go segments = out at *
      obtain ⟨as, body, values⟩ := out
      simpa only using congrArg (fun segments => (⟨segments, schema, check⟩ : Path (v .i32))) h

/-- Capture a write's dynamic scalar, retaining literal NBT at compilation time. -/
public def abstractWrite {v : ObjTy → Type} : Write (v .i32) →
    (as : List ObjTy) × Write (Scope.Var Unit as .i32) × Args v as
  | .literal value => ⟨[], .literal value, .nil⟩
  | .i32 value => ⟨[.i32], .i32 .head, .cons value .nil⟩

public theorem abstractWrite_restore {v : ObjTy → Type} (value : Write (v .i32)) :
    let ⟨_, body, values⟩ := abstractWrite value
    body.map (fun x => x.lookup values) = value := by
  cases value <;> simp [abstractWrite, Write.map]

end Oria.IR.Nbt
