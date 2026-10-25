module

public import Oria.IR.Representation.Physical

namespace Oria.Representation.Table

variable (table : Table) {α : Type} {as : List ObjTy}

/-- Flatten typed field vectors in declaration order. This is the Machine calling convention. -/
@[expose] public def pack {as : List ObjTy} :
    Args (fun a => Vector α (table.width a)) as → Vector α (table.arity as)
  | .nil => #v[]
  | .cons head tail => head ++ pack tail

/-- Recover field boundaries using the same frozen widths as construction and calls. -/
@[expose] public def unpack (as : List ObjTy) (values : Vector α (table.arity as)) :
    Args (fun a => Vector α (table.width a)) as :=
  match as with
  | [] => .nil
  | a :: as =>
      let head := Vector.ofFn fun i : Fin (table.width a) =>
        values[i.val]'(by simp only [arity]; omega)
      let tail := Vector.ofFn fun i : Fin (table.arity as) =>
        values[table.width a + i.val]'(by simp only [arity]; omega)
      .cons head (unpack as tail)

/-- Field reconstruction after flattening preserves every word, including zero-width fields. -/
@[simp] public theorem unpack_pack (xs : Args (fun a => Vector α (table.width a)) as) :
    table.unpack as (table.pack xs) = xs := by
  induction xs with
  | nil => rfl
  | @cons a as head tail ih =>
      simp only [pack, unpack]
      have h : (Vector.ofFn fun i : Fin (table.width a) =>
          (head ++ table.pack tail)[i.val]'(by omega)) = head := by
        ext i hi
        simp
      have t : (Vector.ofFn fun i : Fin (table.arity as) =>
          (head ++ table.pack tail)[table.width a + i.val]'(by omega)) = table.pack tail := by
        ext i hi
        simp
      rw [h, t, ih]

/-- Flattening reconstructed fields neither discards nor duplicates stored words. -/
@[simp] public theorem pack_unpack (values : Vector α (table.arity as)) :
    table.pack (table.unpack as values) = values := by
  induction as with
  | nil => ext i hi; simp [arity] at hi
  | cons a as ih =>
      simp only [unpack, pack, ih]
      ext i hi
      simp only [Vector.getElem_append, Vector.getElem_ofFn]
      split
      · rfl
      · congr 1; omega

/-- Layout round-trip: construction and elimination are inverse at every field boundary. -/
public theorem layout_correct (xs : Args (fun a => Vector α (table.width a)) as)
    (values : Vector α (table.arity as)) :
    table.unpack as (table.pack xs) = xs ∧ table.pack (table.unpack as values) = values :=
  ⟨table.unpack_pack xs, table.pack_unpack values⟩

/-- A projected field is exactly the vector supplied when constructing the aggregate. -/
public theorem project_pack (xs : Args (fun a => Vector α (table.width a)) as)
    (i : Fin as.length) : (table.unpack as (table.pack xs)).get i = xs.get i := by
  rw [unpack_pack]

/-- The scanner map uses exactly the same field flattening as Machine values. -/
public theorem pack_kinds (as : List ObjTy) :
    table.pack (Args.tabulate as (fun i => table.kinds (as.get i))) = table.payload as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [Args.tabulate, pack, payload]
      exact congrArg (fun tail => table.kinds a ++ tail) ih

/-- Every descriptor field slice is precisely that field's pointer classification. -/
public theorem descriptor_correct (as : List ObjTy) (i : Fin as.length) :
    (table.unpack as (table.payload as)).get i = table.kinds (as.get i) := by
  rw [← pack_kinds, unpack_pack, Args.get_tabulate]

end Oria.Representation.Table
