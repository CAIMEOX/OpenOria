module

public import Oria.IR.Representation.Physical
import Std.Data.HashSet

namespace Oria.Representation.Persistent

open Oria Oria.IR

/-- A physical payload action used while promoting one source object. -/
public inductive Action (n : Nat) where
  | scalar
  | copy (target : Fin n)
  | retainRef (target : Fin n)
  deriving Repr

/-- One constructor's persistent heap layout and the actions for its payload words. -/
public structure ConstructorPlan (n : Nat) where
  slots : Nat
  layout : HeapLayout slots
  actions : Vector (Action n) slots
  deriving Repr

/-- A closed promotion node. Edges point into the one finite type graph. -/
public inductive Node (n : Nat) where
  | immediate (type : ObjTy)
  | ref {slots : Nat} (element : ObjTy) (child : Fin n) (layout : HeapLayout slots)
  | boxed (type : ObjTy) (constructors : Array (ConstructorPlan n))
  deriving Repr

namespace Node

/-- The logical type represented by a promotion node. -/
public def type {n : Nat} : Node n → ObjTy
  | .immediate type => type
  | .ref element _ _ => .ref element
  | .boxed type _ => type

end Node

/-- One finite scanner entry. The tag is kept in `layout` and is not part of `scanCode`. -/
public structure Scanner where
  slots : Nat
  layout : HeapLayout slots
  deriving Repr

namespace Scanner

public def code (scanner : Scanner) : Nat := scanner.layout.scanCode

end Scanner

/-- A finite closed graph of promotion nodes and scanner layouts. -/
public structure PlanTable where
  nodeCount : Nat
  nodes : Vector (Node nodeCount) nodeCount
  scanners : Array Scanner
  deriving Repr

namespace PlanTable

/-- Static NBT tag knowledge shares one physical leaf layout and one memoization key. -/
@[expose] public def canonical : ObjTy → ObjTy
  | .nbt _ => .nbt none
  | type => type

/-- Resolve a complete logical type to its bounded promotion-graph index. -/
public def lookup? (plans : PlanTable) (type : ObjTy) : Option (Fin plans.nodeCount) :=
  (List.finRange plans.nodeCount).find? fun index =>
    (plans.nodes.get index).type == canonical type

end PlanTable

private def missingNode {α : Type _} (type : ObjTy) : Except Diagnostic α :=
  throw (.unsupportedRepresentation .anonymous type .body)

private def nodeIndex (types : Array ObjTy) (type : ObjTy) : Except Diagnostic (Fin types.size) :=
  match types.findFinIdx? (· == PlanTable.canonical type) with
  | some index => pure index
  | none => missingNode type

private def children (table : Table) : ObjTy → Except Diagnostic (Array ObjTy)
  | .nbtRef _ => throw .mutableNbtPersistence
  | .unit | .bool | .i32 | .nbt _ => pure #[]
  | .option element | .ref element => pure #[element]
  | .data id => do
      let some schema := table.schema? id
        | throw (.unknownObjectType id)
      let fields := schema.constructors.flatMap (·.fields)
      let ⟨_, args⟩ := id
      pure (args ++ fields).toArray

/-- Query a closed type graph, including erased type arguments, without constructing physical plans. -/
public def reachableTypes (table : Table) (roots : Array ObjTy) : Except Diagnostic (Array ObjTy) := do
  let mut pending := roots.toList.reverse.toArray
  let mut visited : Std.HashSet ObjTy := {}
  let mut types : Array ObjTy := #[]
  while let some type := pending.back? do
    pending := pending.pop
    let type := PlanTable.canonical type
    unless visited.contains type do
      visited := visited.insert type
      types := types.push type
      let next ← children table type
      pending := pending ++ next.toList.reverse.toArray
  pure types

private def checkLayout {slots : Nat} (layout : HeapLayout slots) : Except Diagnostic (HeapLayout slots) :=
  if slots ≤ 30 then pure layout
  else throw (.persistentLayoutTooWide layout.type slots)

private def actionsFor {slots : Nat}
    (types : Array ObjTy) (payload : Vector WordKind slots) :
    Except Diagnostic (Vector (Action types.size) slots) :=
  Vector.ofFnM fun index =>
    match payload.get index with
    | .scalar => pure .scalar
    | .pointer type => do
        let target ← nodeIndex types type
        match type with
        | .ref _ => pure (.retainRef target)
        | _ => pure (.copy target)

private def constructorPlan {slots : Nat}
    (types : Array ObjTy) (layout : HeapLayout slots) :
    Except Diagnostic (ConstructorPlan types.size) := do
  let layout ← checkLayout layout
  let actions ← actionsFor types layout.payload
  pure ⟨_, layout, actions⟩

private def optionPlan
    (table : Table) (types : Array ObjTy) (element : ObjTy) :
    Except Diagnostic (Array (ConstructorPlan types.size)) := do
  let noneLayout ← table.layout (.none : Constructor (.option element) [])
  let someLayout ← table.layout (.some : Constructor (.option element) [element])
  let nonePlan ← constructorPlan types noneLayout
  let somePlan ← constructorPlan types someLayout
  pure #[nonePlan, somePlan]

private def dataConstructorPlan
    (table : Table) (types : Array ObjTy) (owner : TypeId)
    (constructor : ConstructorSchema) : Except Diagnostic (ConstructorPlan types.size) := do
  let reference : Constructor (.data owner) constructor.fields := .data ⟨constructor.name⟩
  constructorPlan types (← table.layout reference)

private def buildNode
    (table : Table) (types : Array ObjTy) (type : ObjTy) :
    Except Diagnostic (Node types.size) :=
  match type with
  | .nbtRef _ => throw .mutableNbtPersistence
  | .unit | .bool | .i32 => pure (.immediate type)
  | .nbt _ =>
      pure (.boxed type #[⟨0, ⟨type, `Oria.Nbt.Data, 0, #v[]⟩, #v[]⟩])
  | .ref element => do
      let child ← nodeIndex types element
      let layout ← checkLayout (table.refLayout element)
      pure (.ref element child layout)
  | .option element =>
      .boxed type <$> optionPlan table types element
  | .data id => do
      let some schema := table.schema? id
        | throw (.unknownObjectType id)
      if table.boxed type then
        let constructors ← schema.constructors.toArray.mapM
          (dataConstructorPlan table types id)
        pure (.boxed type constructors)
      else
        pure (.immediate type)

private def nodeLayouts {n : Nat} : Node n → List Scanner
  | .immediate _ => []
  | .ref _ _ layout => [⟨_, layout⟩]
  | .boxed _ constructors => constructors.toList.map fun constructor =>
      ⟨_, constructor.layout⟩

private def collectScanners {n : Nat} (nodes : Vector (Node n) n) : Array Scanner := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut scanners : Array Scanner := #[]
  for node in nodes.toList do
    for scanner in nodeLayouts node do
      unless seen.contains scanner.code do
        seen := seen.insert scanner.code
        scanners := scanners.push scanner
  return scanners

/-- Build one closed persistent promotion graph for all demanded root and memory types. -/
public def build (table : Table) (roots : Array ObjTy) : Except Diagnostic PlanTable := do
  let types ← reachableTypes table roots
  let nodes ← Vector.ofFnM fun index => buildNode table types types[index]
  pure ⟨types.size, nodes, collectScanners nodes⟩

end Oria.Representation.Persistent
