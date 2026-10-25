module

public import Oria.Std.Command.Arg
public import Oria.Language.Nbt

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Compound command arguments

`Compound` supplies an NBT compound through host data, fields containing dynamic holes, or a
runtime compound snapshot. Its codec reuses the NBT formatter, fragment combinators, and
native NBT macro serialization. The receiving command interprets the compound's schema.
-/

namespace Oria.Std.Command.Arg

/-- An NBT compound parameter assembled at construction time or supplied at runtime. -/
public inductive Compound where
  /-- A host compound, rendered as checked SNBT. -/
  | value : Nbt.Value .compound → Compound
  /-- Compound fields with static leaves and typed dynamic holes. Field values must encode NBT. -/
  | fields : List (Nbt.Key × Oria.Command.Fragment EncodedVal) → Compound
  /-- A runtime compound snapshot using Minecraft's native SNBT serialization. -/
  | dynamic : {r : Region} → Val (Nbt.Data (some .compound)) r → Compound

public instance : Oria.Command.ArgCodec Compound where
  key := ⟨`minecraft.argument.nbt_compound⟩
  encode
    | .value value => .nbt value
    | .fields fields => .nbtCompound fields
    | .dynamic value => Nbt.native value

/-- Requirements of the field fragments. Host compounds and snapshot holes add none. -/
@[expose] public def Compound.requirements (value : Compound) : ReqRow :=
  (Oria.Command.encode value).requirements

@[simp] public theorem Compound.value_requirements (value : Nbt.Value .compound) :
    (Compound.value value).requirements = Req.none := rfl

@[simp] public theorem Compound.dynamic_requirements {r : Region}
    (value : Val (Nbt.Data (some .compound)) r) :
    (Compound.dynamic value).requirements = Req.none := rfl

@[simp] public theorem Compound.encode_fragment_requirements (value : Compound) :
    (Oria.Command.encode value).fragment.requirements = value.requirements := rfl

end Oria.Std.Command.Arg
