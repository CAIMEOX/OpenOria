module

public import Oria.Proofs.Nbt.Support
meta import Oria.Proofs.Nbt.Support

namespace Oria.Proofs.Nbt

open Oria.Nbt

structure Base where
  x : Int32

structure Extended extends Base where
  label : String
  deriving ToNbt, FromNbt

structure Plain where
  value : Value .intArray
  enabled : Bool := true
  deriving ToNbt, FromNbt

inductive Impossible : Type
  deriving ToNbt, FromNbt

#guard (ToNbt.toNbt (Extended.mk ⟨7⟩ "demo")).2.renderSnbt.toOption =
  some "{\"x\":7,\"label\":\"demo\"}"
#guard (FromNbt.fromNbt (a := Extended) ⟨_, nbt% {x: 7, label: "demo"}⟩).toOption.map (·.x) = some 7
#guard (FromNbt.fromNbt (a := Plain) ⟨_, nbt% {value: [I; 1, 2], enabled: false}⟩).isOk
#guard !(FromNbt.fromNbt (a := Plain) ⟨_, nbt% {value: [1, 2], enabled: false}⟩).isOk
#guard (FromNbt.fromNbt (a := Plain) ⟨_, nbt% {value: [I; 1]}⟩).toOption.isNone
#guard !(FromNbt.fromNbt (a := Impossible) ⟨_, nbt% "anything"⟩).isOk

/-- error: NBT deriving requires distinct field or constructor labels -/
#guard_msgs(error, substring := true) in
inductive Namespaced where
  | left.mk
  | right.mk
  deriving ToNbt

/-- error: NBT deriving supports non-recursive datatypes -/
#guard_msgs(error, substring := true) in
inductive Chain where
  | nil
  | cons (head : Int32) (tail : Chain)
  deriving FromNbt

/-- error: NBT deriving supports datatypes without indices -/
#guard_msgs(error, substring := true) in
inductive Indexed : Nat → Type where
  | zero : Indexed 0
  deriving ToNbt

/-- error: NBT deriving requires a custom instance for proof-bearing fields -/
#guard_msgs(error, substring := true) in
structure Checked where
  value : Int32
  valid : value = value
  deriving FromNbt

/-- error: NBT deriving requires a custom instance for dependent fields -/
#guard_msgs(error, substring := true) in
structure Dependent where
  n : Nat
  i : Fin n
  deriving FromNbt

#guard (DecodeError.mk [.key ⟨"players"⟩, .index 2, .key ⟨"points"⟩] (.tag .int .long)).pretty 100 =
  "$.\"players\"[2].\"points\": expected int, got long"

end Oria.Proofs.Nbt
