module

meta import Oria.Std.Manifest

public import Oria.Meta.Collect
public import Oria.Std.Manifest
public import Oria.Compiler.Program
public import Oria.Proofs.Fixtures.CommandClosure
public import Oria.Proofs.Fixtures.Envelope
import Oria.Proofs.McFunctionUtil
meta import Oria.Meta.Collect
meta import all Oria.IR.Program.Closed
meta import Oria.Compiler.Program
meta import Oria.Proofs.Fixtures.CommandClosure
meta import Oria.Proofs.Fixtures.Envelope
meta import Oria.Proofs.McFunctionUtil

namespace Oria.Proofs.ClosedProgram

open Oria Oria.IR Oria.Program
open Lean Lean.Elab Command
open Oria.Proofs.Fixtures Oria.Proofs.McFunctionUtil
open Oria.Proofs.Fixtures.CommandClosure

@[mcfunction] private def leaf (x : Val Int32) : Prog .pure Int32 := Prog.pure x
@[mcfunction] private def middle (x : Val Int32) : Prog .pure Int32 := leaf.call x
@[mcfunction] private def root (x : Val Int32) : Prog .pure Int32 := middle.call x

@[mcfunction]
private def sibling (x : Val Int32) : Prog .pure Int32 := do
  let _ ← leaf.call x
  middle.call x

@[mcfunction]
private def duplicateEdge (x : Val Int32) : Prog .pure Int32 := do
  let _ ← leaf.call x
  leaf.call x

@[mcfunction]
private def objectRoot (_ : Val Envelope) : Prog .pure Unit :=
  Prog.pure Val.unit

private def closeCertified
    (entries : Array IR.DeclRef.Some) : CommandElabM Compiler.CompiledProgram := do
  let .ok commands := Std.Manifest.commandCatalog
    | throwError "standard command catalogue did not build"
  let .ok candidate := Oria.collect (← getEnv) entries commands
    | throwError "fixture program did not collect"
  let .ok collected := candidate.checkClosure | throwError "fixture closure was unavailable"
  let .ok closed := Program.compile collected | throwError "fixture program did not compile"
  pure closed

private def close (entries : Array IR.DeclRef.Some) : CommandElabM ClosedProgram := do
  return (← closeCertified entries).closed

example
    (program : ClosedProgram)
    (left right : ClosedRoot program.members)
    (same : left.member.source = right.member.source) :
    left.position = right.position :=
  program.sameRootPosition same

run_cmd do
  let closed ← close #[⟨_, root.ref⟩,
    ⟨_, sibling.ref⟩]
  unless closed.members.size == 4 do throwError "not every transitive member was compiled"
  have _ := closed.closure.memberOrigins
  have _ := closed.closure.memberIndex
  have _ := closed.closure.rootReferences
  let some rootEntry := closed.roots[0]? | throwError "root entry is absent"
  let some siblingEntry := closed.roots[1]?
    | throwError "sibling entry is absent"
  unless rootEntry.member.signature == siblingEntry.member.signature &&
      rootEntry.member.source != siblingEntry.member.source do
    throwError "same-signature roots lost their distinct references"

run_cmd do
  let certified ← closeCertified #[⟨_, duplicateEdge.ref⟩]
  let closed := certified.closed
  let some caller := closed.member? ``duplicateEdge | throwError "caller was not compiled"
  unless closed.members.size == 2 && caller.dependencies.functions.size == 2 do
    throwError "edge multiplicity or member uniqueness changed"
  let _body : IR.Cont.Def caller.signature := caller.body
  have _ := certified.certificate.everyMemberCompiled
  have _ := caller.dependenciesCorrect

run_cmd do
  let closed ← close #[⟨_, leaf.ref⟩,
    ⟨_, leaf.ref⟩]
  unless closed.members.size == 1 && closed.roots.size == 2 do
    throwError "public aliases did not share one compiled member"
  let some entry := closed.roots[0]? | throwError "entry lookup failed"
  unless entry.member.signature == leaf.signature && entry.member.dependencies.functions.isEmpty do
    throwError "typed public entry changed"

run_cmd do
  let closed ← close #[
    ⟨_, moveAndRead.ref⟩,
    ⟨_, objectRoot.ref⟩]
  unless closed.members.any (fun member => member.source == ``moveAndRead) &&
      closed.members.any (fun member => member.source == ``objectRoot) do
    throwError "catalog-linked member was not compiled"

run_cmd do
  let entries := #[⟨_, root.ref⟩,
    ⟨_, sibling.ref⟩]
  let left ← close entries
  let right ← close entries.reverse
  unless left.members.map (fun member => member.source) ==
        right.members.map (fun member => member.source) &&
      left.roots.map (fun root => root.member.source) ==
        (right.roots.map (fun root => root.member.source)).reverse do
    throwError "closed program order depends on source root order"

end Oria.Proofs.ClosedProgram
