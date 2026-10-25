module

public import Oria.IR.Cont.Syntax

namespace Oria.Analysis.Memory

open Oria.IR Oria.IR.Cont

/-- Native list indices are relative to the end when negative. -/
public def resolveIndex (length index : Int) : Int :=
  if index < 0 then length + index else index

/-- Distinct constant indices on the same side of zero cannot select the same list element. -/
public def separateIndices (a b : Int32) : Bool :=
  decide (a.toInt ≠ b.toInt ∧ (a.toInt < 0 ↔ b.toInt < 0))

/-- Signed-index separation is independent of the current list length. -/
public theorem separateIndices_sound (a b : Int32) (length : Int)
    (h : separateIndices a b = true) : resolveIndex length a.toInt ≠ resolveIndex length b.toInt := by
  have h := of_decide_eq_true h
  unfold resolveIndex
  split <;> split <;> omega

/-- Path footprints include descendants: replacing a parent can affect every suffix.
The first unequal keys or provably distinct indices separate two selections. -/
public def separatePaths {Γ : List ObjTy} :
    List (Oria.Nbt.PathSegment (Atom Γ .i32)) →
    List (Oria.Nbt.PathSegment (Atom Γ .i32)) → Bool
  | .key a :: as, .key b :: bs => a != b || separatePaths as bs
  | .index a :: as, .index b :: bs =>
      if a = b then separatePaths as bs else
        match a, b with
        | .i32 a, .i32 b => separateIndices a b
        | _, _ => false
  | _, _ => false

/-- Arena handles and named storage inhabit separate address spaces. -/
public inductive Root (Γ : List ObjTy) where
  | arena {s : Oria.Nbt.Schema} : Scope.Var Unit Γ (.nbtRef s) → Root Γ
  | storage : Datapack.ResourcePath → Root Γ

/-- A canonical absolute selection. Storage prefixes are part of the path itself. -/
public structure Location (Γ : List ObjTy) where
  root : Root Γ
  path : List (Oria.Nbt.PathSegment (Atom Γ .i32))

namespace Location

@[expose] public def ofPath {Γ as : List ObjTy}
    (args : Args (Atom Γ) as) (root : IR.Nbt.Base as)
    (path : IR.Nbt.Path (Scope.Var Unit as .i32)) : Location Γ :=
  let suffix := path.segments.map (·.map (fun x => x.lookup args))
  match root with
  | .arena root => match root.lookup args with
      | .local root => ⟨.arena root, suffix⟩
  | .global ref =>
      ⟨.storage ref.storage, (ref.path.head :: ref.path.tail).map
        (·.map (fun i => Atom.i32 (Int32.ofInt i))) ++ suffix⟩

public def rename {Γ Δ : List ObjTy} (ρ : Scope.Renaming Unit Unit Γ Δ)
    (loc : Location Γ) : Location Δ :=
  ⟨match loc.root with | .arena root => .arena (ρ root) | .storage id => .storage id,
    loc.path.map (·.map (fun x => x.rename ρ))⟩

/-- Must-alias requires both the same bound root and the same semantic path. -/
public def same {Γ : List ObjTy} (a b : Location Γ) : Bool :=
  (match a.root, b.root with
    | .arena a, .arena b => a.index.val == b.index.val
    | .storage a, .storage b => a == b
    | _, _ => false) && decide (a.path = b.path)

/-- Roots may alias inside one arena; distinct storages and owned address spaces are separate. -/
public def separate {Γ : List ObjTy} (a b : Location Γ) : Bool :=
  match a.root, b.root with
  | .arena _, .arena _ => separatePaths a.path b.path
  | .storage x, .storage y => x != y || separatePaths a.path b.path
  | _, _ => true

end Location
end Oria.Analysis.Memory
