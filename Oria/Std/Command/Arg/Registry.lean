module

public import Oria.Std.Command.Arg.Nbt

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Registry descriptions

Loot tables, item modifiers, and slot definitions share resource-or-inline syntax. The
registry index keeps their interfaces distinct while ArgCodec handles the common grammar.
Named and arbitrary inline descriptions retain a conservative context requirement.
Semantic constructors can establish a smaller requirement when their behavior is known.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode ResourceOrTag)

public instance : Oria.Command.ArgCodec ResourceOrTag where
  key := ⟨`minecraft.argument.resource_or_tag⟩
  encode := ResourceOrTag.fragment

@[simp] public theorem ResourceOrTag.encode_requirements (v : Oria.Command.ResourceOrTag) :
    (encode v).requirements = Req.none := by
  cases v <;> simp [encode, Oria.Command.ArgCodec.encode, Oria.Command.ResourceOrTag.fragment,
    Oria.Command.EncodedArg.requirements, Req.none]

@[simp] public theorem ResourceOrTag.encode_fragment_requirements (v : Oria.Command.ResourceOrTag) :
    (encode v).fragment.requirements = Req.none := ResourceOrTag.encode_requirements v

/-- A resource-or-inline value indexed by its native registry contract. -/
public structure RegistryValue (k : Lean.Name) where
  private mk ::
  /-- Encoded native description. -/
  fragment : Oria.Command.Fragment EncodedVal
  /-- Context needed to interpret the description, retained independently of syntax. -/
  requirements : ReqRow

namespace RegistryValue

/-- Reference an external resource with a conservative interpretation contract. -/
public def named {k : Lean.Name} (id : ResourceId) : RegistryValue k :=
  ⟨(encode id).fragment, Req.all⟩

/-- Supply an arbitrary native description, including typed dynamic holes.
The fragment must use the receiving registry's SNBT schema. -/
public def inline {k : Lean.Name} (f : Oria.Command.Fragment EncodedVal) : RegistryValue k :=
  ⟨f, Req.all ||| f.requirements⟩

/-- Construct an inline registry description using the host ToNbt interface. -/
public def ofNbt {k : Lean.Name} {a : Type u} [Nbt.ToNbt a] (value : a) : RegistryValue k :=
  .inline (.nbt (Nbt.ToNbt.toNbt value).2)

public instance {k : Lean.Name} : Oria.Command.ArgCodec (RegistryValue k) where
  key := ⟨k⟩
  encode v := {v.fragment with requirements := v.requirements}

@[simp] public theorem encode_fragment_requirements {k : Lean.Name} (v : RegistryValue k) :
    (encode v).fragment.requirements = v.requirements := rfl

@[simp] public theorem encode_requirements {k : Lean.Name} (v : RegistryValue k) :
    (encode v).requirements = v.requirements := rfl

@[simp] public theorem named_requirements {k : Lean.Name} (id : ResourceId) :
    (named (k := k) id).requirements = Req.all := private_decl% (by
  rfl)

end RegistryValue

/-- Native item-modifier description. -/
public abbrev ItemModifier := RegistryValue `minecraft.argument.item_modifier

/-- Native loot-table description. -/
public abbrev LootTable := RegistryValue `minecraft.argument.loot_table

/-- Native slot-source registry description. -/
public abbrev SlotDefinition := RegistryValue `minecraft.argument.slot_definition

/-- Native predicate resource or inline description. Named and arbitrary inline forms
retain the external definition's conservative context requirement. -/
public abbrev Predicate := RegistryValue `minecraft.argument.predicate

namespace ItemModifier

/-- Set or add a constant/runtime integer count. Native stack limits and modifier semantics apply.
The constant provider reads no context beyond the command's own loot-context construction. -/
public def setCount (count : Scalar) (add : Bool := false) : ItemModifier := private_decl% (
  ⟨.nbtCompound [
    (⟨"type"⟩, .nbt (.string "minecraft:set_count")),
    (⟨"count"⟩, (encode count).fragment),
    (⟨"add"⟩, .nbt (.byte (if add then 1 else 0)))], Req.none⟩)

@[simp] public theorem setCount_requirements (count : Scalar) (add : Bool) :
    (setCount count add).requirements = Req.none := private_decl% (by rfl)

end ItemModifier

/-- Named or inline world-generation feature. Native placement supplies its world, origin,
generator, and random source independently of the command executor. -/
public abbrev Feature := RegistryValue `minecraft.argument.feature

namespace Feature

/-- Reference a feature interpreted in the placement context. -/
public def named (id : ResourceId) : Feature := private_decl% (
  ⟨(encode id).fragment, Req.none⟩)

/-- Supply a native feature description with static fields and typed dynamic holes.
The placement context supplies native world-generation inputs. -/
public def inline (f : Oria.Command.Fragment EncodedVal) : Feature := private_decl% (
  ⟨f, f.requirements⟩)

/-- Serialize a host feature description through ToNbt. Minecraft checks the feature schema. -/
public def ofNbt {a : Type u} [Nbt.ToNbt a] (value : a) : Feature :=
  inline (.nbt (Nbt.ToNbt.toNbt value).2)

@[simp] public theorem named_requirements (id : ResourceId) :
    (named id).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem inline_requirements (f : Oria.Command.Fragment EncodedVal) :
    (inline f).requirements = f.requirements := private_decl% (by rfl)

@[simp] public theorem ofNbt_requirements {a : Type u} [Nbt.ToNbt a] (value : a) :
    (ofNbt value).requirements = Req.none := by simp [ofNbt]

end Feature
end Oria.Std.Command.Arg
