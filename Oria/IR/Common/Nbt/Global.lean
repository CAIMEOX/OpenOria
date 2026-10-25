module

public import Oria.Nbt.Description
public import Oria.Datapack.Resource
public import Oria.Data.Sealed
import all Oria.Data.Sealed

namespace Oria.IR.Nbt

/-- Global roots are compound-field paths. Runtime indices belong to typed selections. -/
@[expose] public def FieldPath (path : Oria.Nbt.Path) : Prop :=
  ∀ segment ∈ path.head :: path.tail, match segment with
    | .key _ => True
    | _ => False

public instance (path : Oria.Nbt.Path) : Decidable (FieldPath path) := by
  let _ : DecidablePred (fun segment : Oria.Nbt.PathSegment => match segment with
      | .key _ => True
      | _ => False) := fun segment => by cases segment <;> infer_instance
  unfold FieldPath
  infer_instance

/-- A pack-relative native location and its schema, retained through every IR. -/
public structure GlobalRef where
  storage : Datapack.ResourcePath
  path : Oria.Nbt.Path
  schema : Oria.Nbt.Schema
  fields : FieldPath path
  deriving DecidableEq

/-- The construction-time initial contents of a global document. -/
public structure GlobalDecl where
  private mk ::
  private representation : Sealed Unit (GlobalRef × Oria.Nbt.Any)

public def GlobalDecl.ref (decl : GlobalDecl) : GlobalRef := private_decl% decl.representation.get.1

public def GlobalDecl.initial (decl : GlobalDecl) : Oria.Nbt.Any := private_decl% decl.representation.get.2

end Oria.IR.Nbt
