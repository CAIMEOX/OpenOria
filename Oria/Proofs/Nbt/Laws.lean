module

import Oria.Proofs.Nbt.Deriving

namespace Oria.Proofs.Nbt

open Oria.Nbt

attribute [local simp] Decode.record Decode.field Decode.fields Encode.record Encode.list
  Decode.arguments Decode.values Decode.element bind pure Except.bind Except.pure
  Std.HashMap.getElem?_insertIfNew Std.HashMap.getElem_insertIfNew Std.HashMap.mem_insertIfNew

example (v : Int8) : FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by simp
example (v : Int16) : FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by simp
example (v : Int64) : FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by simp
example (v : Float32) : FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by simp
example (v : Float) : FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by simp

example {a : Type} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (xs : List a) :
    FromNbt.fromNbt (ToNbt.toNbt xs) = Except.ok xs := from_to_list h xs

example {a : Type} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (xs : Array a) :
    FromNbt.fromNbt (ToNbt.toNbt xs) = Except.ok xs := from_to_array h xs

example {a : Type} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (x : Option a) :
    FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x := from_to_option h x

example (p : Player) : FromNbt.fromNbt (ToNbt.toNbt p) = Except.ok p := by
  change instFromNbtPlayer.fromNbt (instToNbtPlayer.toNbt p) = _
  cases p
  simp [instFromNbtPlayer.fromNbt, instToNbtPlayer.toNbt]

example (c : Choice) : FromNbt.fromNbt (ToNbt.toNbt c) = Except.ok c := by
  cases c <;> rfl

example (s : State) : FromNbt.fromNbt (ToNbt.toNbt s) = Except.ok s := by
  change instFromNbtState.fromNbt (instToNbtState.toNbt s) = _
  cases s <;>
    simp [instFromNbtState.fromNbt, instToNbtState.toNbt]

example {a : Type} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (b : Box a) :
    FromNbt.fromNbt (ToNbt.toNbt b) = Except.ok b := by
  change instFromNbtBox.fromNbt (instToNbtBox.toNbt b) = _
  cases b
  simp [instFromNbtBox.fromNbt, instToNbtBox.toNbt, h]

example {a : Type} [ToNbt a] [FromNbt a]
    (h : ∀ x : a, FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x) (x : Envelope a) :
    FromNbt.fromNbt (ToNbt.toNbt x) = Except.ok x := by
  change instFromNbtEnvelope.fromNbt (instToNbtEnvelope.toNbt x) = _
  cases x <;> simp [instFromNbtEnvelope.fromNbt, instToNbtEnvelope.toNbt, h]

end Oria.Proofs.Nbt
