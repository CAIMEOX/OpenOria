module

public import Oria.IR.Program.Collected
public import Oria.IR.Cont.Definition
public import Lean.Data.NameMap.Basic

namespace Oria.Program

open Oria IR

public structure CompiledMember (program : CollectedProgram) where
  private mk ::
  source : Lean.Name
  signature : Signature
  body : IR.Cont.Def signature
  dependencies : IR.Tree.Dependencies
  origin : CollectedMember
  sourceCorrect : source = origin.definition.source
  signatureCorrect : signature = origin.definition.signature
  dependenciesCorrect : dependencies = origin.dependencies

variable {program : CollectedProgram} {members : Array (CompiledMember program)}

/-- A compilation root resolved to one member of the compiled program. -/
public structure ClosedRoot (members : Array (CompiledMember program)) where
  private mk ::
  position : Fin members.size

namespace ClosedRoot


@[expose] public def member (root : ClosedRoot members) : CompiledMember program :=
  members[root.position]

/-- Reconstruct the typed source declaration from the resolved member. -/
@[expose] public def reference (root : ClosedRoot members) : DeclRef.Some :=
  ⟨root.member.signature, ⟨.named root.member.source⟩⟩

end ClosedRoot

public structure ProgramClosure
    (program : CollectedProgram)
    (members : Array (CompiledMember program))
    (index : Lean.NameMap (Fin members.size))
    (roots : Array (ClosedRoot members)) : Prop where
  everyMemberCompiled : members.size = program.candidate.members.size
  memberOrigins : members.toList.map (fun member => member.origin) =
    program.candidate.members.toList
  memberSourcesNodup : (members.toList.map (fun member => member.source)).Nodup
  indexSize : index.size = members.size
  memberIndex : ∀ position : Fin members.size,
    index.find? members[position].source = some position
  rootReferences : roots.toList.map ClosedRoot.reference = program.candidate.roots.toList
  sourceDependenciesRetained : ∀ member ∈ members,
    member.dependencies = member.origin.dependencies

public structure ClosedProgram where
  private mk ::
  collected : CollectedProgram
  members : Array (CompiledMember collected)
  private index : Lean.NameMap (Fin members.size)
  roots : Array (ClosedRoot members)
  closure : ProgramClosure collected members index roots

namespace ClosedProgram

public def position? (program : ClosedProgram) (name : Lean.Name) :
    Option (Fin program.members.size) :=
  private_decl% program.index.find? name

public def member? (program : ClosedProgram) (name : Lean.Name) :
    Option (CompiledMember program.collected) :=
  (program.position? name).map fun position => program.members[position]

/-- Repeated roots share the same compiled member. -/
public theorem sameRootPosition
    (program : ClosedProgram)
    {left right : ClosedRoot program.members}
    (same : left.member.source = right.member.source) :
    left.position = right.position := by
  have leftIndexed := program.closure.memberIndex left.position
  have rightIndexed := program.closure.memberIndex right.position
  change program.index.find? left.member.source = some left.position at leftIndexed
  rw [same] at leftIndexed
  exact Option.some.inj (leftIndexed.symm.trans rightIndexed)

end ClosedProgram

end Oria.Program
