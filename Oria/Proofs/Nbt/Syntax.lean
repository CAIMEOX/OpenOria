module

import Oria.Nbt
meta import Oria.Nbt

namespace Oria.Proofs.Nbt

open Oria.Nbt

def notice (n : Int32) (s : String) : Value .compound :=
  nbt% {text: $(s), count: $(n), values: [1, "two", {active: true}]}

example (n : Int32) (s : String) : notice n s =
    .compound (.cons ⟨"text"⟩ (.string s)
      (.cons ⟨"count"⟩ (.int n)
        (.cons ⟨"values"⟩ (.list (.cons (.int 1) (.cons (.string "two")
          (.cons (.compound (.cons ⟨"active"⟩ (.byte 1) .nil)) .nil)))) .nil))) := rfl

example : (nbt% -128b) = Value.byte (-128) := rfl
example : (nbt% 32767s) = Value.short 32767 := rfl
example : (nbt% -2147483648) = Value.int (-2147483648) := rfl
example : (nbt% 9223372036854775807L) = Value.long 9223372036854775807 := rfl
example : (nbt% [L; 1, -3]) = Value.longArray #[1, -3] := rfl
example : (nbt% [B; 1, 2b]) = Value.byteArray #[1, 2] := rfl
example (n : Int32) : (nbt% [I; $(n), 2]) = Value.intArray #[n, 2] := rfl

#guard (nbt% {speed: 1.25f, size: 2.5d}).renderSnbt.toOption =
  some "{\"speed\":1.25f,\"size\":2.5d}"

example : (nbt% 100000000000000000000f) = Value.float 100000000000000000000 := rfl
example : (nbt% 100000000000000000000d) = Value.double 100000000000000000000 := rfl
example : (nbt% {}) = Value.compound .nil := rfl
example : (nbt% []) = Value.list .nil := rfl
example : (nbt% [B;]) = Value.byteArray #[] := rfl
example : (nbt% [I;]) = Value.intArray #[] := rfl
example : (nbt% [L;]) = Value.longArray #[] := rfl
example (v : Any) : (nbt% {nested: $(v)}) =
    Value.compound (.cons ⟨"nested"⟩ v.2 .nil) := rfl
example (v : Value .compound) : (nbt% [$(v), $(v)]) =
    Value.list (.cons v (.cons v .nil)) := rfl
example (n : Int32) : (nbt% $(#[n, n + 1])) =
    Value.list (.cons (.int n) (.cons (.int (n + 1)) .nil)) := by
  simp [ToNbt.toNbt, Values.ofValues]
example (B I L : Int32) : (nbt% [I; $(B), $(I), $(L)]) =
    Value.intArray #[B, I, L] := rfl

/-- error: NBT integer literal is outside the signed 8-bit range -/
#guard_msgs(error, substring := true) in
example := nbt% 128b

/-- error: NBT integer literal is outside the signed 32-bit range -/
#guard_msgs(error, substring := true) in
example := nbt% 2147483648

/-- error: SNBT does not support non-finite floating-point literals -/
#guard_msgs(error, substring := true) in
example := nbt% 1e1000d

/-- error: the element's integer type is wider than the NBT array type -/
#guard_msgs(error, substring := true) in
example := nbt% [B; 1s]

end Oria.Proofs.Nbt
