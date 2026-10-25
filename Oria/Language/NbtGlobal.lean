module

public import Oria.IR.Common.Nbt.Global
public import Oria.Data.Sealed
import all Oria.Data.Sealed
import all Oria.IR.Common.Nbt.Global

namespace Oria.Nbt

/-- An owned, named native document. Register it with `Datapack.global` before use.
The address is construction-time data; the contents live in Minecraft storage. -/
public structure Global (a : Type) [Repr a] where
  private mk ::
  private declaration : Sealed a IR.Nbt.GlobalDecl

/-- Declare a pack-relative storage subtree and its first-load contents. The datapack's
namespace qualifies the storage. Reloading a matching schema preserves the current value.
The root path contains only compound fields. -/
public def Global.init {a : Type} [r : Repr a] (storage : Datapack.ResourcePath) (path : Path)
    (initial : a) (fields : IR.Nbt.FieldPath path := by decide) : Global a :=
  private_decl% ⟨Sealed.mk ⟨Sealed.mk (⟨storage, path, r.schema, fields⟩, ToNbt.toNbt initial)⟩⟩

/-- Read-only declaration metadata used by datapack registration and compilation. -/
public def Global.definition {a : Type} [Repr a] (global : Global a) : IR.Nbt.GlobalDecl :=
  private_decl% global.declaration.get

/-- A global declaration retains the schema selected by its source representation. -/
public theorem Global.init_ref {a : Type} [r : Repr a] (storage : Datapack.ResourcePath) (path : Path)
    (initial : a) (fields : IR.Nbt.FieldPath path) :
    (Global.init storage path initial fields).definition.ref = ⟨storage, path, r.schema, fields⟩ :=
  private_decl% (by simp [Global.init, Global.definition, IR.Nbt.GlobalDecl.ref, Sealed.get_mk])

/-- The declared initial contents satisfy their source codec's round-trip law. -/
public theorem Global.init_decodes {a : Type} [r : Repr a] (storage : Datapack.ResourcePath) (path : Path)
    (initial : a) (fields : IR.Nbt.FieldPath path) :
    FromNbt.fromNbt (Global.init storage path initial fields).definition.initial = Except.ok initial :=
  private_decl% (by
    simpa [Global.init, Global.definition, IR.Nbt.GlobalDecl.initial, Sealed.get_mk] using Repr.roundTrip initial)

end Oria.Nbt
