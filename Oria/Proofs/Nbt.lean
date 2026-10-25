module

import Oria.Nbt
import Oria.Proofs.Nbt.Syntax
import Oria.Proofs.Nbt.Decode
import Oria.Proofs.Nbt.Deriving
import Oria.Proofs.Nbt.Laws
import Oria.Proofs.Nbt.Edges
import Lean.Data.Json.Parser
meta import Oria.Nbt

namespace Oria.Proofs.Nbt

open Oria.Nbt

example : Value .compound :=
  .compound (.cons ⟨"text"⟩ (.string "Hello") (.cons ⟨"count"⟩ (.int 3) .nil))

example : Value .list :=
  .list (.cons (.int 1) (.cons (.string "two") .nil))

#guard (Value.compound (.cons ⟨"x"⟩ (.int 1) .nil)).renderSnbt.toOption = some "{\"x\":1}"
#guard (Value.list (.cons (.int 1) (.cons (.string "two") .nil))).renderSnbt.toOption = some "[1,\"two\"]"
#guard (Value.string "line\n\"quoted\"").pretty 80 = "\"line\\n\\\"quoted\\\"\""
#guard !(Value.float ((1 : Float32) / 0)).renderSnbt.isOk
#guard !(nbt% {nested: [$(Value.double (0 / 0))]}).renderSnbt.isOk
#guard (nbt% {"a\"b": "$(literal)\n"}).renderSnbt.toOption =
  some "{\"a\\\"b\":\"\\u0024(literal)\\n\"}"
#guard (Value.double (-0.0)).renderSnbt.toOption = some "-0.0d"
#guard (Value.float (-0.0)).renderSnbt.toOption = some "-0.0f"
#guard (Value.double 0.00000001).renderSnbt.toOption != some "0d"

private def roundTrip (v : Float) : Bool :=
  match (Oria.Nbt.Value.double v).renderSnbt with
  | .error _ => false
  | .ok text => match Lean.Json.parse (text.dropEnd 1).toString with
    | .ok (.num n) => n.toFloat.toBits == v.toBits
    | _ => false

#guard [1.2345678901234567, 1e-8, 1e-200, 1e200, -1e-8,
  Float.ofBits 1, Float.ofBits 0x7fefffffffffffff].all roundTrip
#guard ((nbt% {items: [1, 2, 3]}).pretty 8).contains '\n'
#guard (nbt% {items: [1, 2, 3]}).renderSnbt.toOption = some "{\"items\":[1,2,3]}"
#guard ((Path.key "root key").child (.index (-1))).format.pretty 80 = "\"root key\"[-1]"
#guard (Path.key "price$").format.pretty 80 = "\"price$\""
#guard (Path.key "a\"b\\c").format.pretty 80 = "\"a\\\"b\\\\c\""

example (n : Int32) : (ToNbt.toNbt n).1 = .int := rfl
example (s : String) : (ToNbt.toNbt s).1 = .string := rfl
example {t : Tag} (value : Value t) : (ToNbt.toNbt value).2 = value := rfl

end Oria.Proofs.Nbt
