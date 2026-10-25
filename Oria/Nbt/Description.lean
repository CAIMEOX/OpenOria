module

public import Oria.Nbt.Decode
public import Oria.Nbt.Lemmas
public import Oria.Data.Sealed
import all Oria.Data.Sealed
import Init.LawfulBEqTactics

namespace Oria.Nbt

/-- A finite description of native NBT structure. Fields are required; record readers
may retain additional native fields. Variant payloads use positional NBT lists. -/
public inductive Schema where
  | atom (tag : Tag)
  | boolean
  | enumeration (names : List String)
  | list (element : Schema)
  | record (fields : List (String × Schema))
  | variant (cases : List (String × List Schema))
  deriving Hashable, Repr

/- Lean's equality deriving does not support this nested description. The mutually
recursive comparison follows its lists explicitly, as the object-type comparison does. -/
mutual
  private def equal (a b : Schema) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | (apply isFalse; intro h; cases h; done) | skip
    · rename_i a b
      exact decidable_of_iff (a = b) (by simp)
    · exact isTrue rfl
    · rename_i a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      let _ := equal a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      let _ := equalFields a b
      exact decidable_of_iff (a = b) (by simp)
    · rename_i a b
      let _ := equalCases a b
      exact decidable_of_iff (a = b) (by simp)
  termination_by sizeOf a

  private def equalFields (a b : List (String × Schema)) : Decidable (a = b) := by
    cases a with
    | nil => cases b <;> simp <;> infer_instance
    | cons x xs => cases b with
      | nil => exact isFalse (by intro h; cases h)
      | cons y ys =>
        let _ := equal x.2 y.2
        let _ := equalFields xs ys
        exact decidable_of_iff (x.1 = y.1 ∧ x.2 = y.2 ∧ xs = ys) (by simp [Prod.ext_iff, and_assoc])
  termination_by sizeOf a
  decreasing_by all_goals simp_wf; cases x; simp_all; omega

  private def equalTypes (a b : List Schema) : Decidable (a = b) := by
    cases a with
    | nil => cases b <;> simp <;> infer_instance
    | cons x xs => cases b with
      | nil => exact isFalse (by intro h; cases h)
      | cons y ys =>
        let _ := equal x y
        let _ := equalTypes xs ys
        exact decidable_of_iff (x = y ∧ xs = ys) (by simp)
  termination_by sizeOf a

  private def equalCases (a b : List (String × List Schema)) : Decidable (a = b) := by
    cases a with
    | nil => cases b <;> simp <;> infer_instance
    | cons x xs => cases b with
      | nil => exact isFalse (by intro h; cases h)
      | cons y ys =>
        let _ := equalTypes x.2 y.2
        let _ := equalCases xs ys
        exact decidable_of_iff (x.1 = y.1 ∧ x.2 = y.2 ∧ xs = ys) (by simp [Prod.ext_iff, and_assoc])
  termination_by sizeOf a
  decreasing_by all_goals simp_wf; cases x; simp_all; omega
end

public instance : DecidableEq Schema := private_decl% equal
public instance : BEq Schema := ⟨fun a b => decide (a = b)⟩
public instance : LawfulBEq Schema where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

/-- One source type's native representation and its host codec law. -/
public class Repr (a : Type) extends ToNbt a, FromNbt a where
  private mk ::
  schema : Schema
  roundTrip (v : a) : fromNbt (toNbt v) = Except.ok v

/-- A field selector retains its source/target types and the host projection equation.
Its constructor is confined to the deriving implementation. -/
public structure Field (a b : Type) [Repr a] [Repr b] where
  private mk ::
  key : Key
  get : a → b
  projection (v : a) :
    Decode.record (ToNbt.toNbt v) >>= (fun fs => Decode.field fs key.text) = .ok (get v)

/-- An owned mutable native document. Object code carries a handle; native contents stay
in the invocation arena. Construction and mutation use typed NBT operations. -/
public structure Ref (a : Type) [Repr a] where
  private mk ::

/-- A singular schema-directed selection. Its index carrier is chosen by the stage. -/
public structure Access (i : Type) (a b : Type) [Repr a] [Repr b] where
  private mk ::
  private segments : Sealed (a, b) (List (PathSegment i))

namespace Access

public def root {i a : Type} [Repr a] : Access i a a := private_decl% ⟨Sealed.mk []⟩

public opaque field {i a b : Type} [Repr a] [Repr b] (f : Field a b) : Access i a b :=
  private_decl% ⟨Sealed.mk [.key f.key]⟩

public def «then» {i a b c : Type} [Repr a] [Repr b] [Repr c]
    (p : Access i a b) (q : Access i b c) : Access i a c :=
  private_decl% ⟨Sealed.mk (p.segments.get ++ q.segments.get)⟩

set_option backward.privateInPublic true in
@[noinline] private opaque raw {i a b : Type} [Repr a] [Repr b]
    (p : Access i a b) : List (PathSegment i) :=
  p.segments.get

end Access

public instance {t : Tag} : Repr (Value t) := private_decl% ⟨.atom t, from_to_value⟩

public instance : Repr Int8 := private_decl% ⟨.atom .byte, from_to_int8⟩

public instance : Repr Int16 := private_decl% ⟨.atom .short, from_to_int16⟩

public instance : Repr Int32 := private_decl% ⟨.atom .int, from_to_int32⟩

public instance : Repr Int64 := private_decl% ⟨.atom .long, from_to_int64⟩

public instance : Repr Float32 := private_decl% ⟨.atom .float, from_to_float32⟩

public instance : Repr Float := private_decl% ⟨.atom .double, from_to_float⟩

public instance : Repr String := private_decl% ⟨.atom .string, from_to_string⟩

public instance : Repr Bool := private_decl% ⟨.boolean, from_to_bool⟩

public instance : Repr Unit := private_decl% ⟨.record [], from_to_unit⟩

public instance {a : Type} [r : Repr a] : Repr (Array a) :=
  private_decl% ⟨.list r.schema, from_to_array r.roundTrip⟩

public instance {a : Type} [r : Repr a] : Repr (List a) :=
  private_decl% ⟨.list r.schema, from_to_list r.roundTrip⟩

public instance {a : Type} [r : Repr a] : Repr (Option a) := private_decl%
  ⟨.variant [("none", []), ("some", [r.schema])], from_to_option r.roundTrip⟩

public def Access.at {i a b : Type} [Repr a] [Repr b]
    (p : Access i a (Array b)) (index : i) : Access i a b :=
  private_decl% ⟨Sealed.mk (p.segments.get ++ [.index index])⟩

public instance {i a b : Type} [Repr a] [Repr b] : Coe (Field a b) (Access i a b) :=
  ⟨Access.field⟩

public def Field.at {i a b : Type} [Repr a] [Repr b]
    (p : Field a (Array b)) (index : i) : Access i a b := (Access.field p).at index

end Oria.Nbt
