module

public import Oria.IR.Common.Type

namespace Oria

/-- One first-order type expression in a datatype's parameter telescope. -/
public inductive TypeTemplate where
  | param (index : Nat)
  | nbt (tag : Option Nbt.Tag)
  | app (name : Lean.Name) (args : List TypeTemplate)
  deriving BEq, Repr

namespace TypeTemplate

/-- Instantiate source type parameters before the pure compiler receives a schema. -/
public def instantiate (params : Array ObjTy) : TypeTemplate → Option ObjTy
  | .param i => params[i]?
  | .nbt tag => some (.nbt tag)
  | .app name args => do
      let args ← args.attach.mapM fun a => instantiate params a.val
      match name, args with
      | ``Unit, [] => pure .unit
      | ``Bool, [] => pure .bool
      | ``Int32, [] => pure .i32
      | ``Option, [a] => pure (.option a)
      | `Oria.Persistent.Ref, [a] => pure (.ref a)
      | name, args => pure (.data ⟨name, args⟩)
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have smaller := List.sizeOf_lt_of_mem a.property
  omega

end TypeTemplate

/-- Source labels and the type template used by both deriving and schema instantiation. -/
public structure FieldDecl where
  label : Lean.Name
  type : TypeTemplate
  deriving Repr

public structure ConstructorDecl where
  name : Lean.Name
  fields : List FieldDecl
  deriving Repr

/-- Source declaration's representation choice, resolved after type arguments are closed. -/
public inductive ReprHint where
  | ordinary
  | value
  deriving BEq, DecidableEq, Repr

public structure ObjectDecl where
  name : Lean.Name
  params : Nat
  constructors : List ConstructorDecl
  repr : ReprHint := .ordinary
  deriving Repr

/-- A constructor instantiated at closed object types. -/
public structure ConstructorSchema where
  name : Lean.Name
  fields : List ObjTy
  deriving BEq, DecidableEq, Repr

/-- A closed nominal schema. Representation is chosen from its retained fields. -/
public structure ObjectSchema where
  id : TypeId
  constructors : List ConstructorSchema
  repr : ReprHint := .ordinary
  deriving BEq, DecidableEq, Repr

namespace ObjectDecl

public def instantiate (decl : ObjectDecl) (args : List ObjTy) : Option ObjectSchema := do
  guard (args.length == decl.params)
  let constructors ← decl.constructors.mapM fun c => do
    let fields ← c.fields.mapM fun f => f.type.instantiate args.toArray
    pure { name := c.name, fields : ConstructorSchema }
  pure { id := ⟨decl.name, args⟩, constructors, repr := decl.repr }

end ObjectDecl

end Oria
