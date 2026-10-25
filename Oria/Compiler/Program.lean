module

public import Oria.Compiler.Certificate
import all Oria.IR.Program.Closed

namespace Oria.Program

open Oria IR

private structure CompiledResult
    (program : CollectedProgram) (member : CollectedMember) where
  compiled : CompiledMember program
  origin : compiled.origin = member
  compiledCorrect :
    Compiler.compile program.functions program.objects program.commands compiled.origin.definition =
      .ok (by
        exact compiled.signatureCorrect ▸ compiled.body)

private def compileMember
    (program : CollectedProgram) (member : CollectedMember) :
    Except Diagnostic (CompiledResult program member) :=
  match compiled : Compiler.compile program.functions program.objects program.commands
      member.definition with
  | .error diagnostic => .error diagnostic
  | .ok body => .ok ⟨⟨member.definition.source, member.definition.signature, body,
      member.dependencies, member, rfl, rfl, rfl⟩, rfl, compiled⟩

private structure CompiledList
    (program : CollectedProgram) (source : List CollectedMember) where
  members : List (CompiledMember program)
  origins : members.map (fun member => member.origin) = source
  everyMemberCompiled :
    ∀ member ∈ members,
      Compiler.compile program.functions program.objects program.commands member.origin.definition =
        .ok (member.signatureCorrect ▸ member.body)

private def compileList (program : CollectedProgram) :
    (source : List CollectedMember) →
    Except Diagnostic (CompiledList program source)
  | [] => .ok ⟨[], rfl, by simp⟩
  | member :: rest => do
      let ⟨compiled, origin, compiledCorrect⟩ ← compileMember program member
      let tail ← compileList program rest
      pure ⟨compiled :: tail.members, by simp [origin, tail.origins], by
        intro candidate membership
        simp only [List.mem_cons] at membership
        rcases membership with rfl | membership
        · simpa [origin] using compiledCorrect
        · exact tail.everyMemberCompiled candidate membership⟩

private def memberIndex {program : CollectedProgram} (members : Array (CompiledMember program)) :
    Lean.NameMap (Fin members.size) :=
  (List.finRange members.size).foldl
    (fun index position => index.insert members[position].source position) {}

private def closeRoot
    {program : CollectedProgram}
    (members : Array (CompiledMember program))
    (index : Lean.NameMap (Fin members.size)) :
    (source : DeclRef.Some) →
      Except Diagnostic {root : ClosedRoot members // root.reference = source}
  | ⟨sig, ⟨.named name⟩⟩ =>
      match index.find? name with
      | none => .error (.unknownFunction name)
      | some position =>
          let member := members[position]
          if source : member.source = name then
            if signature : sig = member.signature then
              .ok ⟨⟨position⟩, by
                cases signature
                simp only [ClosedRoot.reference, ClosedRoot.member]
                change DeclRef.Some.mk member.signature ⟨.named member.source⟩ =
                  DeclRef.Some.mk member.signature ⟨.named name⟩
                rw [source]⟩
            else
              .error (.functionSignatureMismatch name sig member.signature)
          else
            .error (.unknownFunction name)

private def closeRoots
    (program : CollectedProgram)
    (members : Array (CompiledMember program))
    (index : Lean.NameMap (Fin members.size)) :
    Except Diagnostic {roots : List (ClosedRoot members) //
      roots.map ClosedRoot.reference = program.candidate.roots.toList} :=
  go program.candidate.roots.toList
where
  go (source : List DeclRef.Some) :
      Except Diagnostic {roots : List (ClosedRoot members) //
        roots.map ClosedRoot.reference = source} :=
    match source with
    | [] => .ok ⟨[], rfl⟩
    | entry :: rest => do
        let ⟨entry, same⟩ ← closeRoot members index entry
        let ⟨entries, sources⟩ ← go rest
        pure ⟨entry :: entries, by simp [same, sources]⟩

public def compile (program : CollectedProgram) : Except Diagnostic Compiler.CompiledProgram := do
  let batch ← compileList program program.candidate.members.toList
  let members := batch.members.toArray
  let index := memberIndex members
  let ⟨closedRoots, sources⟩ ← closeRoots program members index
  let roots := closedRoots.toArray
  have memberSize : members.size = program.candidate.members.size := by
    have sizes := congrArg List.length batch.origins
    simpa [members] using sizes
  if nodup : (members.toList.map (fun member => member.source)).Nodup then
    if exact : ∀ position : Fin members.size,
        index.find? members[position].source = some position then
      if indexSize : index.size = members.size then
        let closed : ClosedProgram := private_decl% ⟨program, members, index, roots, ⟨memberSize,
          by simpa [members] using batch.origins, nodup, indexSize, exact,
          by simpa [roots] using sources,
          fun member _ => member.dependenciesCorrect⟩⟩
        have closedCollected : closed.collected = program := private_decl% rfl
        pure ⟨closed, {
          everyMemberCompiled := by
            cases closedCollected
            intro member membership
            exact batch.everyMemberCompiled member (by simpa [closed, members] using membership)
        }⟩
      else throw (.unknownFunction .anonymous)
    else
      throw (.unknownFunction .anonymous)
  else
    throw (.unknownFunction .anonymous)

end Oria.Program
