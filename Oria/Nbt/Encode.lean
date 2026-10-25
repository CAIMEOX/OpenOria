module

public import Oria.Nbt.Basic

namespace Oria.Nbt

universe u

/-- Conversion from a host value to its NBT tag and payload. -/
public class ToNbt (a : Type u) where
  toNbt : a → Any

namespace Encode

@[expose] public def list (values : List Any) : Any :=
  ⟨.list, .list (values.foldr (fun value rest => .cons value.2 rest) .nil)⟩

@[expose] public def record (fields : List (String × Any)) : Any :=
  ⟨.compound, .compound (fields.foldr
    (fun (key, value) rest => .cons ⟨key⟩ value.2 rest) .nil)⟩

@[expose] public def variant (name : String) (args : List Any) : Any :=
  record [(name, list args)]

end Encode

public instance {t : Tag} : ToNbt (Value t) where
  toNbt value := ⟨t, value⟩

public instance : ToNbt Any where
  toNbt := id

public instance : ToNbt Int8 where
  toNbt value := ⟨.byte, .byte value⟩

public instance : ToNbt Int16 where
  toNbt value := ⟨.short, .short value⟩

public instance : ToNbt Int32 where
  toNbt value := ⟨.int, .int value⟩

public instance : ToNbt Int64 where
  toNbt value := ⟨.long, .long value⟩

public instance : ToNbt Float32 where
  toNbt value := ⟨.float, .float value⟩

public instance : ToNbt Float where
  toNbt value := ⟨.double, .double value⟩

public instance : ToNbt String where
  toNbt value := ⟨.string, .string value⟩

public instance : ToNbt Bool where
  toNbt value := ⟨.byte, .byte (if value then 1 else 0)⟩

public instance : ToNbt Unit where
  toNbt _ := ⟨.compound, .compound .nil⟩

public instance {a : Type u} [ToNbt a] : ToNbt (Option a) where
  toNbt
    | none => Encode.variant "none" []
    | some value => Encode.variant "some" [ToNbt.toNbt value]

public instance {a : Type u} [ToNbt a] : ToNbt (Array a) where
  toNbt values := ⟨.list, .list (Values.ofValues (values.map ToNbt.toNbt))⟩

public instance {a : Type u} [ToNbt a] : ToNbt (List a) where
  toNbt values := ⟨.list, .list (values.foldr (fun value rest =>
    let ⟨_, value⟩ := ToNbt.toNbt value
    .cons value rest) .nil)⟩

end Oria.Nbt
