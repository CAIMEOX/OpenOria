module

public import Oria.Nbt.Basic
public import Oria.Nbt.Description
import Init.LawfulBEqTactics

namespace Oria

mutual
  /-- A nominal datatype instantiated at closed object-language types. -/
  public structure TypeId where
    name : Lean.Name
    args : List ObjTy := []
    deriving Hashable, Repr

  /-- Logical object data types. -/
  public inductive ObjTy where
    | unit
    | bool
    | i32
    | option (element : ObjTy)
    | ref (element : ObjTy)
    | data (id : TypeId)
    | nbt (tag : Option Nbt.Tag)
    | nbtRef (schema : Nbt.Schema)
    deriving Hashable, Repr
end

/- Lean's DecidableEq deriving handler does not yet support nested mutual types. -/
mutual
  private def eqType (a b : ObjTy) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | (apply isFalse; intro h; cases h; done) | skip
    · exact .isTrue rfl
    · exact .isTrue rfl
    · exact .isTrue rfl
    · rename_i a b
      let _ := eqType a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      let _ := eqType a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      let _ := eqId a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      exact decidable_of_iff (a = b) (by simp)
  termination_by sizeOf a

  private def eqId (a b : TypeId) : Decidable (a = b) := by
    cases a with | mk n xs =>
      cases b with | mk m ys =>
        let _ := eqTypes xs ys
        exact decidable_of_iff (n = m ∧ xs = ys) (by simp)
  termination_by sizeOf a

  private def eqTypes (xs ys : List ObjTy) : Decidable (xs = ys) := by
    cases xs with
    | nil => cases ys <;> simp <;> infer_instance
    | cons x xs =>
      cases ys with
      | nil => exact .isFalse (by intro h; cases h)
      | cons y ys =>
        let _ := eqType x y
        let _ := eqTypes xs ys
        exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
  termination_by sizeOf xs
end

public instance : DecidableEq ObjTy := private_decl% eqType
public instance : DecidableEq TypeId := private_decl% eqId

public instance : BEq ObjTy := ⟨fun a b => decide (a = b)⟩
public instance : BEq TypeId := ⟨fun a b => decide (a = b)⟩
public instance : LawfulBEq ObjTy where
  rfl := by intro a; change decide (a = a) = true; simp
  eq_of_beq := by intro a b h; change decide (a = b) = true at h; exact of_decide_eq_true h
public instance : LawfulBEq TypeId where
  rfl := by intro a; change decide (a = a) = true; simp
  eq_of_beq := by intro a b h; change decide (a = b) = true at h; exact of_decide_eq_true h

public theorem TypeId.args_size (id : TypeId) : sizeOf id.args < sizeOf id := by
  cases id
  simp
  omega


end Oria
