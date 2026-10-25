module

public import Oria.Std.Command.Arg
public import Oria.Nbt.Encode

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Dialog arguments

`DialogContent` selects a loaded dialog resource, an inline host-constructed description,
or a literal notice. Named and inline contents retain the full context requirement.
Literal notices add no context requirements. The target Minecraft version interprets the
full schema. See [Dialog](##Oria.Std.Dialog) for the standard command interface.
-/

namespace Oria.Std.Command.Arg

/-- A dialog resource reference or inline description. -/
public inductive DialogContent where
  /-- Reference a loaded dialog registry resource with a conservative full context requirement. -/
  | named : ResourceId → DialogContent
  /-- A native command fragment with optional dynamic numeric fields and full context requirements. -/
  | inline : Oria.Command.Fragment EncodedVal → DialogContent
  /-- A notice with literal title and body, independent of execution context. -/
  | notice : String → String → DialogContent

/-- Construct an inline dialog through a host ToNbt instance.
Minecraft validates the dialog schema when parsing the command. -/
@[expose] public def DialogContent.ofNbt {a : Type} [Nbt.ToNbt a] (value : a) : DialogContent :=
  .inline (.nbt (Nbt.ToNbt.toNbt value).2)

public instance : Oria.Command.ArgCodec DialogContent where
  key := ⟨`minecraft.argument.dialog⟩
  encode
    | .named id => .require Req.all (Oria.Command.encode id).fragment
    | .inline value => .require Req.all value
    | .notice title message => .nbt (nbt% {
        type: "minecraft:notice", title: $(title),
        body: {type: "minecraft:plain_message", contents: $(message)}
      })

@[simp] public theorem DialogContent.ofNbt_requirements {a : Type} [Nbt.ToNbt a] (value : a) :
    (Oria.Command.encode (DialogContent.ofNbt value)).requirements = Req.all := by
  simp [DialogContent.ofNbt, Oria.Command.encode, Oria.Command.ArgCodec.encode,
    Oria.Command.EncodedArg.requirements, Oria.Command.Fragment.require,
    Oria.Command.Fragment.nbt, Req.none]

@[simp] public theorem DialogContent.notice_requirements (title message : String) :
    (Oria.Command.encode (DialogContent.notice title message)).requirements = Req.none := rfl

end Oria.Std.Command.Arg
