module

public import Oria.Std.Command.Arg
public import Oria.Nbt.Encode

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Text component arguments

Text components carry the context needed to interpret their contents. Literal text and
integer interpolation are context-independent. Arbitrary NBT components retain the full
context requirement, since they may contain selectors, score references, or NBT references.
These descriptions exist at construction time and use the ordinary command-fragment codec.
-/

namespace Oria.Std.Command.Arg

/-- A text component with a known interpretation contract. -/
public inductive TextComponent where
  /-- Literal text, independent of execution context. -/
  | literal : String → TextComponent
  /-- Static or dynamic integer interpolation, independent of execution context. -/
  | number : Scalar → TextComponent
  /-- An arbitrary host NBT component, conservatively requiring the full context. -/
  | raw : Nbt.Any → TextComponent

namespace TextComponent

/-- Construct a complete host text component through ToNbt. Arbitrary components retain
the full context requirement. -/
@[expose] public def ofNbt {a : Type u} [Nbt.ToNbt a] (value : a) : TextComponent :=
  .raw (Nbt.ToNbt.toNbt value)

/-- Context read when Minecraft interprets this component. -/
@[expose] public def requirements : TextComponent → ReqRow
  | .literal _ | .number _ => Req.none
  | .raw _ => Req.all

public instance : Oria.Command.ArgCodec TextComponent where
  key := ⟨`minecraft.argument.text_component⟩
  encode
    | .literal text => .nbt (nbt% {text: $(text)})
    | .number value => .nbtCompound [
        (⟨"translate"⟩, .nbt (.string "%s")),
        (⟨"with"⟩, .nbtList [(Oria.Command.encode value).fragment])]
    | .raw value => .require Req.all (.nbt value.2)

@[simp] public theorem encode_requirements (value : TextComponent) :
    (Oria.Command.encode value).requirements = value.requirements := by
  cases value with
  | literal _ => rfl
  | raw _ => simp [Oria.Command.encode, Oria.Command.ArgCodec.encode,
      Oria.Command.EncodedArg.requirements, requirements,
      Oria.Command.Fragment.require, Oria.Command.Fragment.nbt, Req.none]
  | number value =>
      cases value <;> simp [Oria.Command.encode, Oria.Command.ArgCodec.encode,
        Oria.Command.EncodedArg.requirements, requirements,
        Oria.Command.Fragment.nbtCompound, Oria.Command.Fragment.nbtList,
        Oria.Command.Fragment.empty, Oria.Command.Fragment.append,
        Oria.Command.Fragment.nbt, Oria.Command.Fragment.token, Req.none]

end TextComponent

end Oria.Std.Command.Arg
