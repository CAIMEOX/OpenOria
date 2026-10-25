module

public import Oria.IR.Catalog.Function
public import Oria.IR.Tree.Dependencies
public import Oria.IR.Catalog.Object

namespace Oria.Program

open Oria IR IR.Tree

/-- One collected definition paired with its single cached dependency observation. -/
public structure CollectedMember where
  definition : ElaboratedDef
  dependencies : Dependencies
  dependenciesCorrect : dependencies = definition.definition.dependencies

/-- Environment-free input to the pure closure checker. -/
public structure CollectionCandidate where
  private mk ::
  roots : Array DeclRef.Some
  members : Array CollectedMember
  schemas : Array ObjectSchema
  commands : Command.Catalog
  persistentRoots : Array RootDefinition := #[]

public def memberForRef? {sig : Signature}
    (candidate : CollectionCandidate) (ref : DeclRef sig) : Option CollectedMember :=
  let .named name := ref.key
  candidate.members.find? fun member => member.definition.source == name

public def refResolved {sig : Signature} (candidate : CollectionCandidate) (ref : DeclRef sig) : Bool :=
  match memberForRef? candidate ref with
  | some member => member.definition.signature == sig
  | none => false

public def rootResolved (candidate : CollectionCandidate) (root : DeclRef.Some) : Bool :=
  refResolved candidate root.ref

public def functionsResolved (candidate : CollectionCandidate) (member : CollectedMember) : Bool :=
  member.dependencies.functions.all fun dependency =>
    refResolved candidate dependency.ref

public def schemaPresent (candidate : CollectionCandidate) (id : TypeId) : Bool :=
  candidate.schemas.any fun schema => schema.id == id

public def typePresent (candidate : CollectionCandidate) : ObjTy → Bool
  | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => true
  | .option element | .ref element => typePresent candidate element
  | .data id => schemaPresent candidate id

public def schemaClosed (candidate : CollectionCandidate) (schema : ObjectSchema) : Bool :=
  schema.constructors.all fun constructor =>
    constructor.fields.all fun field => typePresent candidate field

public def objectsResolved (candidate : CollectionCandidate) (member : CollectedMember) : Bool :=
  member.dependencies.objectTypes.toArray.all (schemaPresent candidate)

public def commandsResolved (candidate : CollectionCandidate) (member : CollectedMember) : Bool :=
  member.dependencies.commands.all fun dependency =>
    (candidate.commands.resolveRef dependency.ref).isOk

private def checkCommandDependencies (catalog : Command.Catalog) :
    (dependencies : List CommandDependency) →
    Except Diagnostic (PLift <| dependencies.all fun dependency =>
      (catalog.resolveRef dependency.ref).isOk)
  | [] => .ok ⟨rfl⟩
  | dependency :: rest =>
      match resolved : catalog.resolveRef dependency.ref with
      | .error diagnostic => .error diagnostic
      | .ok _ =>
          match checkCommandDependencies catalog rest with
          | .error diagnostic => .error diagnostic
          | .ok ⟨restResolved⟩ => .ok ⟨by
              simp only [List.all_cons, Bool.and_eq_true]
              constructor
              · rw [resolved]
                rfl
              · exact restResolved⟩

private def checkMemberCommands (candidate : CollectionCandidate) :
    (members : List CollectedMember) →
    Except Diagnostic (PLift <| members.all (commandsResolved candidate ·))
  | [] => .ok ⟨rfl⟩
  | member :: rest =>
      match checkCommandDependencies candidate.commands member.dependencies.commands.toList with
      | .error diagnostic => .error diagnostic
      | .ok ⟨memberResolved⟩ =>
          match checkMemberCommands candidate rest with
          | .error diagnostic => .error diagnostic
          | .ok ⟨restResolved⟩ =>
              .ok ⟨by
                simp only [List.all_cons, Bool.and_eq_true]
                constructor
                · apply Array.all_eq_true.mpr
                  intro i inBounds
                  apply List.all_eq_true.mp memberResolved
                  simp
                · exact restResolved⟩

private def checkCommands (candidate : CollectionCandidate) :
    Except Diagnostic (PLift <|
      candidate.members.all (commandsResolved candidate ·)) := do
  let ⟨resolved⟩ ← checkMemberCommands candidate candidate.members.toList
  pure ⟨Array.all_eq_true.mpr fun i inBounds =>
    List.all_eq_true.mp resolved candidate.members[i] (by simp)⟩

/-- Five finite closure obligations checked without consulting Environment or Tree representation. -/
public structure CollectionClosed (candidate : CollectionCandidate) : Prop where
  roots : candidate.roots.all (rootResolved candidate) = true
  functions : candidate.members.all (functionsResolved candidate ·) = true
  directObjects : candidate.members.all (objectsResolved candidate ·) = true
  schemaFields : candidate.schemas.all (schemaClosed candidate ·) = true
  commands : candidate.members.all (commandsResolved candidate ·) = true

/-- Candidate sealed with the three catalogs and its pure closure certificate. -/
public structure CollectedProgram where
  private mk ::
  candidate : CollectionCandidate
  objects : ObjectCatalog
  functions : Function.Catalog
  commands : Command.Catalog
  closed : CollectionClosed candidate

namespace CollectionCandidate

public def checkClosure
    (candidate : CollectionCandidate) : Except Diagnostic CollectedProgram := do
  let objects ← ObjectCatalog.build candidate.schemas.toList
  let functions ← Function.Catalog.build (candidate.members.map (·.definition)).toList
  let ⟨commands⟩ ← checkCommands candidate
  if roots : candidate.roots.all (rootResolved candidate) = true then
    if functionEdges : candidate.members.all (functionsResolved candidate ·) = true then
      if directObjects : candidate.members.all (objectsResolved candidate ·) = true then
        if schemaFields : candidate.schemas.all (schemaClosed candidate ·) = true then
          return ⟨candidate, objects, functions, candidate.commands,
            ⟨roots, functionEdges, directObjects, schemaFields, commands⟩⟩
        else throw (.unknownObjectType ⟨.anonymous, []⟩)
      else throw (.unknownObjectType ⟨.anonymous, []⟩)
    else throw (.unknownFunction .anonymous)
  else throw (.unknownFunction .anonymous)

end CollectionCandidate

end Oria.Program
