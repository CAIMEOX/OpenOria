module

public import Oria.IR.Representation.Syntax
public import Oria.Diagnostic
public import Std.Data.HashMap.Basic
import Lean.Util.SCC

namespace Oria.Representation

open Oria.IR

/-- Nominal values use constructor tags, heap pointers, or an inline scalar product. -/
public inductive Form where
  | enumeration
  | boxed
  | product (slots : Nat)
  deriving BEq, DecidableEq, Repr

/-- Frozen representation metadata for a closed schema graph. -/
public structure Table where
  private mk ::
  private schemas : Std.HashMap TypeId ObjectSchema
  private forms : Std.HashMap TypeId Form

namespace Table

public def schema? (table : Table) (id : TypeId) : Option ObjectSchema :=
  table.schemas.get? id

@[expose] public def form (table : Table) (id : TypeId) : Form :=
  private_decl% table.forms.getD id .boxed

/-- The same width determines local values, parameters, results, and stored fields. -/
@[expose, reducible] public def width (table : Table) : ObjTy → Nat
  | .unit => 0
  | .bool | .i32 | .nbt _ | .nbtRef _ | .option _ | .ref _ => 1
  | .data id => match table.form id with | .product n => n | _ => 1

@[expose, reducible] public def arity (table : Table) : List ObjTy → Nat
  | [] => 0
  | a :: as => table.width a + table.arity as

@[simp] public theorem arity_append (table : Table) (as bs : List ObjTy) :
    table.arity (as ++ bs) = table.arity as + table.arity bs := by
  induction as with
  | nil => simp [arity]
  | cons a as ih => simp [arity, ih, Nat.add_assoc]

public def boxed (table : Table) : ObjTy → Bool
  | .option _ | .ref _ | .nbt _ | .nbtRef _ => true
  | .data id => table.form id == .boxed
  | _ => false

public def product (table : Table) : ObjTy → Bool
  | .data id => match table.form id with | .product _ => true | _ => false
  | _ => false

/-- A nominal schema with one constructor needs payload projection but no tag test. -/
public def singleConstructor (table : Table) : ObjTy → Bool
  | .data id => (table.schema? id).any (·.constructors.length == 1)
  | _ => false

private def scalarWidth (forms : Std.HashMap TypeId Form) (owner : TypeId) :
    ObjTy → Except Diagnostic Nat
  | .unit => pure 0
  | .bool | .i32 => pure 1
  | .data id => match forms.get? id with
      | some .enumeration => pure 1
      | some (.product n) => pure n
      | some .boxed => throw (.pointerValueField owner (.data id))
      | none => throw (.unknownObjectType id)
  | a => throw (.pointerValueField owner a)

/-- Lean's dependency-first SCC order resolves products and diagnoses infinite inline layouts. -/
public def build (schemas : Array ObjectSchema) : Except Diagnostic Table := do
  let mut byId : Std.HashMap TypeId ObjectSchema := {}
  for schema in schemas do
    if byId.contains schema.id then throw (.duplicateObjectType schema.id)
    byId := byId.insert schema.id schema
  let edges (id : TypeId) : List TypeId :=
    match byId.get? id with
    | some schema =>
      if schema.repr == .value then
        schema.constructors.flatMap fun c => c.fields.filterMap fun
          | .data id => some id
          | _ => none
      else []
    | none => []
  let mut forms : Std.HashMap TypeId Form := {}
  for group in Lean.SCC.scc (schemas.toList.map (·.id)) edges do
    let [id] := group
      | match group with
        | id :: _ => throw (.recursiveValueType id)
        | [] => continue
    if (edges id).contains id then throw (.recursiveValueType id)
    let some schema := byId.get? id | throw (.unknownObjectType id)
    let shape ← match schema.repr with
      | .ordinary => pure <| if schema.constructors.any (! ·.fields.isEmpty) then .boxed else .enumeration
      | .value => do
        let [ctor] := schema.constructors | throw (.invalidValueType id)
        let widths ← ctor.fields.mapM (scalarWidth forms id)
        pure (.product widths.sum)
    forms := forms.insert id shape
  pure ⟨byId, forms⟩

@[expose] public def kinds (table : Table) : (a : ObjTy) → Vector WordKind (table.width a)
  | .unit => #v[]
  | .bool | .i32 => #v[.scalar]
  | .option a => #v[.pointer (.option a)]
  | .ref a => #v[.pointer (.ref a)]
  | .nbt t => #v[.pointer (.nbt t)]
  | .nbtRef s => #v[.pointer (.nbtRef s)]
  | .data id => match h : table.form id with
      | .boxed => by simpa [width, h] using (#v[WordKind.pointer (.data id)])
      | .enumeration => by simpa [width, h] using (#v[WordKind.scalar])
      | .product n => by simpa [width, h] using (Vector.replicate n WordKind.scalar)

public def refLayout (table : Table) (a : ObjTy) : HeapLayout (table.width a) :=
  ⟨.ref a, `Oria.Persistent.Ref, 0, table.kinds a⟩

@[expose] public def payload (table : Table) : (as : List ObjTy) → Vector WordKind (table.arity as)
  | [] => #v[]
  | a :: as => table.kinds a ++ table.payload as

public def check (table : Table) (source : Lean.Name) (location : RepresentationLocation) :
    ObjTy → Except Diagnostic Unit
  | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => pure ()
  | .option a | .ref a => table.check source location a
  | .data id =>
      if table.schemas.contains id then pure ()
      else throw (.unsupportedRepresentation source (.data id) location)

public def tag {a : ObjTy} {fields : List ObjTy} (table : Table) (ref : Constructor a fields) :
    Except Diagnostic Int32 := do
  match ref with
  | .none => pure 0
  | .some => pure 1
  | .data (owner := owner) ref =>
      let some schema := table.schema? owner | throw (.unknownObjectType owner)
      let some i := schema.constructors.findFinIdx? (·.name == ref.name)
        | throw (.unknownConstructor owner ref.name)
      unless schema.constructors[i].fields == fields do
        throw (.constructorShapeMismatch owner ref.name schema.constructors[i].fields fields)
      if i.val + 1 < 2147483648 then pure (Int32.ofNat (i.val + 1))
      else throw (.invalidObjectSchema owner)

public def layout {a : ObjTy} {fields : List ObjTy} (table : Table) (ref : Constructor a fields) :
    Except Diagnostic (HeapLayout (table.arity fields)) := do
  pure ⟨a, ref.name, ← table.tag ref, table.payload fields⟩

end Table
end Oria.Representation
