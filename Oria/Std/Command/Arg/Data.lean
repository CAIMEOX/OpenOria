module

public import Oria.Std.Command.Arg
public import Oria.Nbt.Encode

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# NBT and computation arguments

`DataTarget` locates game NBT; `DataSource` describes the source of a native modification.
`ComputeContext` and `Provider` describe a number provider's evaluation context and expression.
These host types construct commands, with runtime integers supplied through `Scalar.dynamic`.

Command paths use `Nbt.Path Scalar (Nbt.Value .compound)`: field names and compound filters
are static, while indices may be dynamic. `.all` and `.matching` can select multiple values;
subsequent segments apply to every match. Native get, set from, and append from handle
multiple matches differently; see [Data](##Oria.Std.Data).
-/

namespace Oria.Std.Command.Arg

universe u

/-- Numeric NBT tag used when storing a scaled command result. -/
public inductive NumericTag where
  /-- Signed 8-bit integer. -/
  | byte
  /-- Signed 16-bit integer. -/
  | short
  /-- Signed 32-bit integer. -/
  | int
  /-- Signed 64-bit integer. -/
  | long
  /-- IEEE 754 binary32. -/
  | float
  /-- IEEE 754 binary64. -/
  | double

public instance : Oria.Command.ArgCodec NumericTag where
  key := ⟨`minecraft.argument.numeric_tag⟩
  encode t := .token (match t with
    | .byte => "byte" | .short => "short" | .int => "int"
    | .long => "long" | .float => "float" | .double => "double")

/-- A native NBT location. Entity targets must be singular; blocks must be in accessible chunks. -/
public inductive DataTarget where
  /-- Named storage, independent of the executor. -/
  | storage : ResourceId → DataTarget
  /-- Single-entity NBT. Minecraft restricts mutation; for example, data cannot write player NBT. -/
  | entity : Target → DataTarget
  /-- Block-entity NBT, requiring the dimension and the coordinate's context. -/
  | block : Vec3 → DataTarget

/-- A number provider's native evaluation context. -/
public inductive ComputeContext where
  /-- Use the native default context, reading position and dimension. -/
  | default
  /-- Supply target_entity while retaining the caller's this_entity, position, and dimension. -/
  | entity : Target → ComputeContext
  /-- Supply block state and an available block entity at the selected position. -/
  | block : Vec3 → ComputeContext

/-- A provider description with the context summary established during construction. -/
public structure Provider where
  private mk ::
  private fragment : Oria.Command.Fragment EncodedVal
  /-- Context dependencies established by the provider constructor. -/
  requirements : ReqRow

namespace Provider

/-- Reference a loaded resource whose implementation is external to this expression. -/
public def named (id : ResourceId) : Provider :=
  ⟨(Oria.Command.encode id).fragment, Req.all⟩

/-- An arbitrary provider fragment. Its native interpretation conservatively reads all context. -/
public def inline (fragment : Oria.Command.Fragment EncodedVal) : Provider :=
  ⟨fragment, Req.all ||| fragment.requirements⟩

private def withRequirements (provider : Provider) (requirements : ReqRow) : Provider :=
  { provider with requirements := requirements ||| provider.fragment.requirements }

/-- Constant provider with a static or runtime integer value. The value's producing computation
retains its own effects; provider evaluation reads no additional implicit context. -/
public def scalar (value : Scalar) : Provider :=
  ⟨.nbtCompound [(⟨"type"⟩, .nbt (.string "minecraft:constant")),
    (⟨"value"⟩, (Oria.Command.encode value).fragment)], Req.none⟩

@[simp] public theorem scalar_requirements (value : Scalar) :
    (scalar value).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem named_requirements (id : ResourceId) :
    (named id).requirements = Req.all := private_decl% (by rfl)

@[simp] public theorem inline_requirements (fragment : Oria.Command.Fragment EncodedVal) :
    (inline fragment).requirements = Req.all ||| fragment.requirements := private_decl% (by rfl)

end Provider

/-- Construct a provider from host NBT. Numeric tags become constant descriptions with no
additional context requirement; other tags retain the full requirement. Minecraft checks
the schema, and command planning checks numeric finiteness. -/
public def Provider.ofNbt {a : Type u} [Nbt.ToNbt a] (value : a) : Provider :=
  let value := Nbt.ToNbt.toNbt value
  let fragment := Oria.Command.Fragment.nbt (v := EncodedVal) value.2
  match value.1 with
  | .byte | .short | .int | .long | .float | .double =>
      ⟨.nbtCompound [(⟨"type"⟩, .nbt (.string "minecraft:constant")), (⟨"value"⟩, fragment)], Req.none⟩
  | _ => .inline fragment

@[simp] public theorem Provider.ofNbt_requirements {a : Type u} [Nbt.ToNbt a] (value : a) :
    (Provider.ofNbt value).requirements =
      (match (Nbt.ToNbt.toNbt value).1 with
      | .byte | .short | .int | .long | .float | .double => Req.none
      | _ => Req.all) := private_decl% (by
  unfold Provider.ofNbt
  generalize Nbt.ToNbt.toNbt value = encoded
  rcases encoded with ⟨tag, val⟩
  cases tag <;> simp [Provider.inline, Oria.Command.Fragment.nbt, Req.none])

@[simp] public theorem Provider.i32_requirements (value : Int32) :
    (Provider.ofNbt value).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem Provider.float_requirements (value : Float) :
    (Provider.ofNbt value).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem Provider.float32_requirements (value : Float32) :
    (Provider.ofNbt value).requirements = Req.none := private_decl% (by rfl)

/-- Select integer or floating-point provider evaluation. -/
public inductive Calculation where
  /-- Integer evaluation, writing an IntTag when used as a data compute source. -/
  | integer : Provider → Calculation
  /-- Floating-point evaluation, writing a FloatTag when used as a data compute source. -/
  | float : Provider → Calculation

/-- Provider requirements survive the integer/float registry selection. -/
@[expose] public def Calculation.requirements : Calculation → ReqRow
  | .integer provider | .float provider => provider.requirements

/-- A native NBT modification. The game validates target shapes and indices. -/
public inductive DataOp where
  /-- Replace the target value, taking the last of multiple from-source matches. -/
  | set
  /-- Merge source compounds into target compounds. -/
  | merge
  /-- Append to target lists in source-selection order. -/
  | append
  /-- Prepend to target lists in source-selection order. -/
  | prepend
  /-- Insert at a possibly dynamic index. Negative indices follow native command rules. -/
  | insert : Scalar → DataOp

/-- Native string slicing, indexed by Java UTF-16 code units with an exclusive upper bound.
Negative indices count from the end. Minecraft rejects out-of-bounds or reversed intervals. -/
public inductive Slice where
  /-- Keep the whole string. -/
  | all
  /-- Keep the suffix starting at the given index. -/
  | from : Scalar → Slice
  /-- Keep the given half-open interval. -/
  | between : Scalar → Scalar → Slice

/-- A native data modify source. Its requirements combine those of its constituent arguments. -/
public inductive DataSource where
  /-- An SNBT command fragment with host constants and typed dynamic holes. -/
  | value : Oria.Command.Fragment EncodedVal → DataSource
  /-- Native NBT copying. Omitting the path selects the source's root compound. -/
  | from : DataTarget → Option (Nbt.Path Scalar (Nbt.Value .compound)) → DataSource
  /-- Read a string or the text form of a native scalar, then slice it.
  Lists and compounds are excluded from this text source. -/
  | string : DataTarget → Nbt.Path Scalar (Nbt.Value .compound) → Slice → DataSource
  /-- Evaluate a provider and write a native IntTag or FloatTag. -/
  | compute : ComputeContext → Calculation → DataSource

/-- Construct a static SNBT source through a host ToNbt instance.
Use Data.write to copy runtime snapshots verbatim. -/
@[expose] public def DataSource.ofNbt {a : Type u} [Nbt.ToNbt a] (value : a) : DataSource :=
  .value (.nbt (Nbt.ToNbt.toNbt value).2)

public instance : Oria.Command.ArgCodec Nbt.Path where
  key := ⟨`minecraft.argument.nbt_path⟩
  encode path := ⟨[.literal (.path path)], Req.none⟩

private def pathSegment : Nbt.PathSegment Scalar (Nbt.Value .compound) → Oria.Command.Fragment EncodedVal
  | .key key => ⟨[.literal (.path (Nbt.Path.key key.text))], Req.none⟩
  | .index index => .append (.token "[") <|
      .append (Oria.Command.encode index).fragment (.token "]")
  | .all => .token "[]"
  | .matching pattern => .append (.token "[") <|
      .append (.nbt pattern) (.token "]")

private def pathSuffix (out : Oria.Command.Fragment EncodedVal) (segment : Nbt.PathSegment Scalar (Nbt.Value .compound)) :=
  out.append (match segment with
    | .key _ => .prepend "." (pathSegment segment)
    | _ => pathSegment segment)

/-- Preserve path structure, reuse the integer codec for each index, and emit static filters as SNBT. -/
public instance : Oria.Command.ArgCodec (Nbt.Path Scalar (Nbt.Value .compound)) where
  key := ⟨`minecraft.argument.nbt_path⟩
  encode path := ⟨private_decl% ((path.tail.foldl pathSuffix (pathSegment path.head)).segments), Req.none⟩

namespace Nbt.Path

@[simp] public theorem encode_requirements (value : Nbt.Path) :
    (Oria.Command.encode value).requirements = Req.none := by
  rfl

@[simp] public theorem encode_fragment_requirements (value : Nbt.Path) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  rfl

@[simp] public theorem scalar_encode_requirements (value : Nbt.Path Scalar (Nbt.Value .compound)) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem scalar_encode_fragment_requirements (value : Nbt.Path Scalar (Nbt.Value .compound)) :
    (Oria.Command.encode value).fragment.requirements = Req.none :=
  scalar_encode_requirements value

end Nbt.Path

public instance : Oria.Command.ArgCodec DataTarget where
  key := ⟨`minecraft.argument.data_target⟩
  encode
    | .storage id => .spaced [.token "storage", (Oria.Command.encode id).fragment]
    | .entity target => .spaced [.token "entity", (Oria.Command.encode target).fragment]
    | .block pos => .require Req.dimension <|
        .spaced [.token "block", (Oria.Command.encode pos).fragment]

public instance : Oria.Command.ArgCodec ComputeContext where
  key := ⟨`minecraft.argument.compute_context⟩
  encode
    | .default => .require (Req.position ||| Req.dimension) (.token "default")
    | .entity target => .require (Req.position ||| Req.dimension)
        (Oria.Command.encode (DataTarget.entity target)).fragment
    | .block pos => .require (Req.position ||| Req.dimension)
        (Oria.Command.encode (DataTarget.block pos)).fragment

public instance : Oria.Command.ArgCodec Provider where
  key := ⟨`minecraft.argument.provider⟩
  encode provider := private_decl% { provider.fragment with requirements := provider.requirements }

@[simp] public theorem Provider.encode_requirements (provider : Provider) :
    (Oria.Command.encode provider).requirements = provider.requirements := private_decl% (by rfl)

@[simp] public theorem Provider.encode_fragment_requirements (provider : Provider) :
    (Oria.Command.encode provider).fragment.requirements = provider.requirements :=
  Provider.encode_requirements provider

public instance : Oria.Command.ArgCodec Calculation where
  key := ⟨`minecraft.argument.calculation⟩
  encode
    | .integer provider => .spaced [.token "integer", (Oria.Command.encode provider).fragment]
    | .float provider => .spaced [.token "float", (Oria.Command.encode provider).fragment]

@[simp] public theorem Calculation.encode_fragment_requirements (calculation : Calculation) :
    (Oria.Command.encode calculation).fragment.requirements = calculation.requirements := by
  cases calculation <;> simp only [Calculation.requirements, Oria.Command.encode,
    Oria.Command.ArgCodec.encode, Oria.Command.Fragment.spaced, Oria.Command.Fragment.append,
    Oria.Command.Fragment.token, Oria.Command.Fragment.space, Req.none,
    BitVec.zero_or, BitVec.or_zero]
  all_goals exact Provider.encode_fragment_requirements _

@[simp] public theorem Calculation.encode_requirements (calculation : Calculation) :
    (Oria.Command.encode calculation).requirements = calculation.requirements :=
  Calculation.encode_fragment_requirements calculation

public instance : Oria.Command.ArgCodec DataOp where
  key := ⟨`minecraft.argument.data_operation⟩
  encode
    | .set => .token "set"
    | .merge => .token "merge"
    | .append => .token "append"
    | .prepend => .token "prepend"
    | .insert index => .spaced [.token "insert", (Oria.Command.encode index).fragment]

namespace DataOp

@[simp] public theorem encode_requirements (value : DataOp) :
    (Oria.Command.encode value).requirements = Req.none := by
  cases value with
  | set | merge | append | prepend => rfl
  | insert index =>
      cases index <;>
        simp [Oria.Command.encode, Oria.Command.ArgCodec.encode,
          Oria.Command.EncodedArg.requirements, Req.none]

@[simp] public theorem encode_fragment_requirements (value : DataOp) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by
  simpa [Oria.Command.EncodedArg.requirements] using encode_requirements value

end DataOp

public instance : Oria.Command.ArgCodec DataSource where
  key := ⟨`minecraft.argument.data_source⟩
  encode
    | .value value => .spaced [.token "value", value]
    | .from target path => .spaced <|
        [.token "from", (Oria.Command.encode target).fragment] ++
          path.toList.map (fun path => (Oria.Command.encode path).fragment)
    | .string target path slice => .spaced <|
        [.token "string", (Oria.Command.encode target).fragment,
          (Oria.Command.encode path).fragment] ++
          match slice with
          | .all => []
          | .from start => [(Oria.Command.encode start).fragment]
          | .between start stop => [(Oria.Command.encode start).fragment, (Oria.Command.encode stop).fragment]
    | .compute context calculation => .spaced [
        .token "compute", (Oria.Command.encode context).fragment,
        (Oria.Command.encode calculation).fragment]

namespace DataTarget

/-- Execution context required to access the target. -/
@[expose] public def requirements (value : DataTarget) : ReqRow :=
  (Oria.Command.encode value).requirements

@[simp] public theorem storage_requirements (id : ResourceId) : requirements (.storage id) = Req.none := by
  simp [requirements, Oria.Command.encode, Oria.Command.ArgCodec.encode,
    Oria.Command.EncodedArg.requirements, Oria.Command.Fragment.spaced,
    Oria.Command.Fragment.append, Oria.Command.Fragment.token, Oria.Command.Fragment.space, Req.none]

@[simp] public theorem encode_fragment_requirements (value : DataTarget) :
    (Oria.Command.encode value).fragment.requirements = requirements value := by
  rfl

end DataTarget

namespace ComputeContext

/-- Environment information read when selecting the provider's evaluation context. -/
@[expose] public def requirements (value : ComputeContext) : ReqRow :=
  (Oria.Command.encode value).requirements

end ComputeContext

namespace DataSource

/-- Source context requirements, including the selected compute context and provider summary. -/
@[expose] public def requirements (value : DataSource) : ReqRow :=
  (Oria.Command.encode value).requirements

@[simp] public theorem value_requirements (value : Oria.Command.Fragment EncodedVal) :
    requirements (.value value) = value.requirements := by
  simp [requirements, Oria.Command.encode, Oria.Command.ArgCodec.encode,
    Oria.Command.EncodedArg.requirements, Oria.Command.Fragment.spaced,
    Oria.Command.Fragment.append, Oria.Command.Fragment.token, Oria.Command.Fragment.space, Req.none]

@[simp] public theorem from_requirements (target : DataTarget) (path : Option (Nbt.Path Scalar (Nbt.Value .compound))) :
    requirements (.from target path) = target.requirements := by
  cases path <;>
    simp [requirements, Oria.Command.encode, Oria.Command.ArgCodec.encode,
      Oria.Command.EncodedArg.requirements, Oria.Command.Fragment.spaced,
      Oria.Command.Fragment.append, Oria.Command.Fragment.token, Oria.Command.Fragment.space,
      DataTarget.requirements, Req.none]

@[simp] public theorem ofNbt_requirements {a : Type u} [Nbt.ToNbt a] (value : a) :
    requirements (ofNbt value) = Req.none := by
  simp [ofNbt]

end DataSource

end Oria.Std.Command.Arg
