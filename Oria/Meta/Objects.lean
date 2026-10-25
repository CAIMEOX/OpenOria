module

public import Oria.Meta.ObjectDerive
public import Oria.IR.Representation.Persistent
public import Oria.Diagnostic
import Std.Data.HashSet

namespace Oria.ObjectRegistry

/-- Close the nominal schema graph once from the source registry and complete type identities. -/
public def collect (env : Lean.Environment) (types : Array ObjTy) :
    Except Diagnostic (Array ObjectSchema) := do
  let mut pending := types.toList.reverse.toArray
  let mut seen : Std.HashSet ObjTy := {}
  let mut schemas : Array ObjectSchema := #[]
  while let some type := pending.back? do
    pending := pending.pop
    unless seen.contains type do
      seen := seen.insert type
      match type with
      | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => pure ()
      | .option a | .ref a => pending := pending.push a
      | .data id =>
          let ⟨name, args⟩ := id
          let some entry := find? env name | throw (.unknownObjectType id)
          let some schema := entry.declaration.instantiate args
            | throw (.unknownObjectType id)
          schemas := schemas.push schema
          let next := args ++ schema.constructors.flatMap (·.fields)
          pending := pending ++ next.reverse.toArray
  pure (schemas.qsort fun a b =>
    let ⟨a, _⟩ := a.id
    let ⟨b, _⟩ := b.id
    a.quickLt b)

/-- Source-level persistence checks use the same closed layouts as target generation. -/
public def checkPersistent (env : Lean.Environment) (types : Array ObjTy) :
    Except Diagnostic Unit := do
  let schemas ← collect env types
  let table ← Representation.Table.build schemas
  discard (Representation.Persistent.build table types)

end Oria.ObjectRegistry
