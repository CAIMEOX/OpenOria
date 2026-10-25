module

public import Oria.Nbt.Encode
public import Oria.Nbt.Decode

namespace Oria.Nbt

universe u

@[simp] public theorem Any.eta (v : Any) : (⟨v.1, v.2⟩ : Any) = v := rfl

@[simp] public theorem Decode.expect_value {t : Tag} (v : Value t) : expect t ⟨t, v⟩ = .ok v := by
  simp [expect]

@[simp] public theorem Decode.within_ok {a : Type u} (step : PathSegment) (x : a) :
    within step (.ok x) = .ok x := rfl

@[simp] public theorem from_to_value {t : Tag} (v : Value t) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by
  simp [FromNbt.fromNbt, ToNbt.toNbt]

@[simp] public theorem from_to_any (v : Any) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_int8 (v : Int8) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_int16 (v : Int16) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_int32 (v : Int32) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_int64 (v : Int64) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_float32 (v : Float32) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_float (v : Float) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_string (v : String) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := rfl

@[simp] public theorem from_to_bool (v : Bool) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by cases v <;> rfl

@[simp] public theorem from_to_unit (v : Unit) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by cases v; rfl

private theorem singleton_fields (key : String) (value : Any) :
    (({} : Std.HashMap String Any).insertIfNew key value).toList = [(key, value)] := by
  have len : (({} : Std.HashMap String Any).insertIfNew key value).toList.length = 1 := by
    simp [Std.HashMap.size_insertIfNew]
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp len
  have mem : (key, value) ∈ (({} : Std.HashMap String Any).insertIfNew key value).toList := by
    simp [Std.HashMap.getElem_insertIfNew]
  rw [hp] at mem
  have eq : (key, value) = p := by simpa using mem
  simpa [← eq] using hp

@[simp] public theorem Decode.variant_encode (name : String) (args : List Any) :
    variant (Encode.variant name args) = .ok (name, Encode.list args) := by
  simp [variant, record, Encode.variant, Encode.record, fields, singleton_fields,
    bind, pure, Except.bind, Except.pure]

private theorem decode_list {a : Type u} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (xs : List a) (i : Nat) :
    Decode.list (xs.foldr (fun x rest => .cons (ToNbt.toNbt x).2 rest) .nil) i = .ok xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [List.foldr, Decode.list, h, ih, bind, pure, Except.bind, Except.pure]

public theorem from_to_list {a : Type u} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (xs : List a) :
    FromNbt.fromNbt (ToNbt.toNbt xs) = Except.ok xs := by
  simpa [FromNbt.fromNbt, ToNbt.toNbt, Except.bind] using decode_list h xs 0

public theorem from_to_array {a : Type u} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (xs : Array a) :
    FromNbt.fromNbt (ToNbt.toNbt xs) = Except.ok xs := by
  cases xs with
  | mk xs =>
    simpa [FromNbt.fromNbt, ToNbt.toNbt, Values.ofValues, List.foldr_map, Except.bind, Except.map]
      using congrArg (Except.map List.toArray) (decode_list h xs 0)

public theorem from_to_option {a : Type u} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (v : Option a) :
    FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by
  cases v <;>
    simp [FromNbt.fromNbt, ToNbt.toNbt, Decode.arguments, Encode.list,
      Decode.values, Decode.element, h, bind, pure, Except.bind, Except.map, Except.pure]

end Oria.Nbt
