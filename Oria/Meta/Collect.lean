module

public import Oria.IR.Program.Collected
public import Oria.Command.Catalog
import Oria.Compiler.Lower.Scope
import all Oria.IR.Tree.Elaborated
import all Oria.IR.Tree.Dependencies
import all Oria.IR.Program.Collected
public import Oria.Meta.McFunction
public import Oria.Meta.Persistent
import Oria.Meta.ObjectDerive

namespace Oria

open IR IR.Tree Program

/-- Stable enough ordering for worklists while retaining full `TypeId` equality for visitation. -/
private def typeIdLess (left right : TypeId) : Bool :=
  let ⟨leftName, _⟩ := left
  let ⟨rightName, _⟩ := right
  leftName.quickLt rightName

private def visit (env : Lean.Environment) (candidate : CollectionCandidate)
    (roots : Array DeclRef.Some) (generated : Lean.NameMap ElaboratedDef) :
    Except Diagnostic CollectionCandidate := do
  let persistentRoots := candidate.persistentRoots
  let ordered := roots.qsort fun a b =>
    let .named x := a.ref.key
    let .named y := b.ref.key
    x.quickLt y
  let mut worklist := ordered.reverse
  let mut cache : Lean.NameMap CollectedMember := candidate.members.foldl
    (fun cache member => cache.insert member.definition.source member) {}
  let mut members := candidate.members
  let mut generated := generated
  let mut objectWorklist : Array TypeId := #[]
  while let some requested := worklist.back? do
    worklist := worklist.pop
    let .named name := requested.ref.key
    match cache.find? name with
    | some member =>
        unless member.definition.signature == requested.sig do
          throw (.functionSignatureMismatch name requested.sig member.definition.signature)
    | none =>
      let definition ← match generated.find? name with
        | some definition => pure definition
        | none => McFunctionRegistry.elaborate env name
      unless definition.signature == requested.sig do
        throw (.functionSignatureMismatch name requested.sig definition.signature)
      let lifted := Lower.Scope.lower name definition.definition
      for helper in lifted.helpers do
        generated := generated.insert helper.source helper
      let definition := { definition with definition := lifted.main }
      let dependencies := definition.definition.dependencies
      for dependency in dependencies.roots do
        let some root := persistentRoots.find? (·.ref.name == dependency.ref.name)
          | throw (.unknownRoot dependency.ref.name)
        unless root.initial.signature.result == dependency.type do
          throw (.rootTypeMismatch dependency.ref.name dependency.type root.initial.signature.result)
      let member : CollectedMember := ⟨definition, dependencies, rfl⟩
      cache := cache.insert name member
      members := members.push member
      worklist := worklist ++ dependencies.functions.reverse
      objectWorklist := objectWorklist ++
        (dependencies.objectTypes.toArray.qsort typeIdLess).reverse
  let schemas ← ObjectRegistry.collect env (objectWorklist.map ObjTy.data)
  let schemas := candidate.schemas ++ schemas.filter (fun schema =>
    !candidate.schemas.any (fun old => old.id == schema.id))
  pure { candidate with members, schemas }

/-- Collect every environment-backed definition and closed schema before entering the pure checker. -/
public def collect (env : Lean.Environment) (roots : Array DeclRef.Some)
    (commands : Command.Catalog) (persistentRoots : Array RootDefinition := #[]) :
    Except Diagnostic CollectionCandidate := do
  let initializers := persistentRoots.map (·.initial)
  let roots := roots ++ initializers.map fun initial => ⟨initial.signature, .named initial.source⟩
  let generated := initializers.foldl (fun cache defn => cache.insert defn.source defn) ({} : Lean.NameMap ElaboratedDef)
  let initial : CollectionCandidate := private_decl% { roots, commands, persistentRoots, members := #[], schemas := #[] }
  let candidate ← visit env initial roots generated
  for root in persistentRoots do
    let mut pending := #[root.initial.source]
    let mut checked : Lean.NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      unless checked.contains name do
        checked := checked.insert name
        let some member := candidate.members.find? (·.definition.source == name) | throw (.unknownFunction name)
        unless member.definition.signature.grade.Below (Persistent.stateGrade.seq .failure) do
          throw (.invalidRootInitializer root.ref.name)
        unless member.dependencies.commands.isEmpty && member.dependencies.roots.isEmpty &&
            member.dependencies.globals.isEmpty do
          throw (.invalidRootInitializer root.ref.name)
        pending := pending ++ member.dependencies.functions.map fun dependency =>
          let .named name := dependency.ref.key
          name
  pure candidate

/-- Extend a collected program with runtime definitions, reusing cached user dependencies and schemas. -/
public def includeRuntime (env : Lean.Environment) (candidate : CollectionCandidate)
    (definitions : Array ElaboratedDef) : Except Diagnostic CollectionCandidate := do
  let roots := definitions.map fun defn => (⟨defn.signature, .named defn.source⟩ : DeclRef.Some)
  let generated := definitions.foldl (fun cache defn => cache.insert defn.source defn) ({} : Lean.NameMap ElaboratedDef)
  let extended ← visit env { candidate with roots := candidate.roots ++ roots } roots generated
  let added := extended.members.extract candidate.members.size extended.members.size
  let commands ← added.foldlM (fun commands member =>
    member.dependencies.commands.foldlM (fun commands dependency => commands.add dependency.ref) commands)
    candidate.commands
  pure { extended with commands }

end Oria
