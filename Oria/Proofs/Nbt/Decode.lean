module

import Oria.Proofs.Nbt.Support
meta import Oria.Proofs.Nbt.Support

namespace Oria.Proofs.Nbt

open Oria.Nbt

example (n : Int32) : FromNbt.fromNbt (ToNbt.toNbt n) = Except.ok n := rfl
example {t : Tag} (v : Value t) : FromNbt.fromNbt (ToNbt.toNbt v) = Except.ok v := by
  simp [FromNbt.fromNbt, ToNbt.toNbt, Decode.expect]
example (b : Bool) : FromNbt.fromNbt (ToNbt.toNbt b) = Except.ok b := by cases b <;> rfl

#guard !(FromNbt.fromNbt (a := Int32) ⟨_, nbt% 1L⟩).isOk
#guard !(FromNbt.fromNbt (a := Bool) ⟨_, nbt% 2b⟩).isOk
#guard FromNbt.fromNbt (a := List Int32) ⟨_, nbt% [1, 2]⟩ == .ok [1, 2]
#guard FromNbt.fromNbt (a := Array String) ⟨_, nbt% ["a", "b"]⟩ == .ok #["a", "b"]
#guard FromNbt.fromNbt (a := List Int32) ⟨_, nbt% [1, "two"]⟩ ==
  .error ⟨[.index 1], .tag .int .string⟩
#guard FromNbt.fromNbt (a := Option (Option Int32)) ⟨_, nbt% {some: [{none: []}]}⟩ == .ok (some none)
#guard (ToNbt.toNbt (some (none : Option Int32))).2.renderSnbt.toOption =
  some "{\"some\":[{\"none\":[]}]}"

end Oria.Proofs.Nbt
