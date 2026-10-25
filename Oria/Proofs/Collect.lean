module

meta import Oria.Std.Manifest

import Oria.Std.Manifest

public import Oria.Meta.Collect
public import Oria.Meta.Elab.ProgDo
public import Oria.Proofs.Fixtures.Envelope
public import Oria.Proofs.Fixtures.McFunction
public import Oria.Proofs.Fixtures.CommandClosure
import Oria.Proofs.McFunctionUtil
public import Oria.Std
meta import Oria.Meta.Collect
meta import Oria.Proofs.Fixtures.Envelope
meta import Oria.Proofs.Fixtures.McFunction
meta import Oria.Proofs.Fixtures.CommandClosure
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Std

namespace Oria.Proofs.Collect

open Oria Oria.IR Oria.Program
open Lean Lean.Elab Command
open Oria.Proofs.Fixtures
open Oria.Proofs.Fixtures.CommandClosure
open Oria.Proofs.McFunctionUtil

@[mcfunction]
private def leaf (x : Val Int32) : Prog .pure Int32 :=
  Prog.pure x

@[mcfunction]
private def middle (x : Val Int32) : Prog .pure Int32 :=
  leaf.call x

@[mcfunction]
private def root (x : Val Int32) : Prog .pure Int32 :=
  middle.call x

@[mcfunction]
private def duplicateEdge (x : Val Int32) : Prog .pure Int32 := do
  let _ ← leaf.call x
  leaf.call x

@[mcfunction]
private def envelopeRoot (_ : Val Envelope) : Prog (Grade.handled .pure) Unit :=
  Prog.pure Val.unit

private def absentSig : Command.Signature :=
  { schema := []
    req := Req.none
    eff := Eff.none }

private def absent : Command.Ref absentSig :=
  ⟨`oria.proofs.absent, { parts := [.token (.ofString "absent")] }, none⟩

@[mcfunction]
private def absentCommand :
    Prog absentSig.grade Int32 :=
  Command.emit (absent.call .nil)

private def collectWithStandardCatalog
    (env : Lean.Environment) (roots : Array IR.DeclRef.Some) :
    Except Diagnostic CollectionCandidate := do
  let commands ← Std.Manifest.commandCatalog
  Oria.collect env roots commands

private def collectSpec (entries : Array IR.DeclRef.Some) : CommandElabM CollectionCandidate := do
  let .ok candidate := collectWithStandardCatalog (← getEnv) entries
    | throwError "fixture closure did not collect"
  pure candidate

private def memberNamed (candidate : CollectionCandidate) (name : Lean.Name) : Bool :=
  candidate.members.any fun member => member.definition.source == name

run_cmd do
  let candidate ← collectSpec #[⟨_, root.ref⟩]
  unless candidate.members.size == 3 &&
      memberNamed candidate ``root && memberNamed candidate ``middle &&
      memberNamed candidate ``leaf do
    throwError "transitive function closure changed"
  let .ok program := candidate.checkClosure
    | throwError "transitive closure certificate was unavailable"
  have _ : CollectionClosed program.candidate := program.closed

run_cmd do
  let candidate ← collectSpec #[⟨_, duplicateEdge.ref⟩]
  let some caller := candidate.members.find? fun member => member.definition.source == ``duplicateEdge
    | throwError "caller was not collected"
  unless candidate.members.size == 2 && caller.dependencies.functions.size == 2 do
    throwError "definition deduplication or edge multiplicity changed"

run_cmd do
  let candidate ← collectSpec #[
    ⟨_, leaf.ref⟩,
    ⟨_, leaf.ref⟩
  ]
  unless candidate.members.size == 1 do
    throwError "two aliases collected the same definition more than once"

run_cmd do
  let candidate ← collectSpec #[
    ⟨_, Oria.Proofs.Fixtures.McFunction.increment.ref⟩
  ]
  unless memberNamed candidate ``Oria.Proofs.Fixtures.McFunction.increment do
    throwError "persistent registry dependency was not collected"

run_cmd do
  let candidate ← collectSpec #[⟨_, envelopeRoot.ref⟩]
  unless candidate.schemas.find? (fun schema => schema.id == Envelope.Oria.id) ==
        some Envelope.Oria.schema &&
      candidate.schemas.find? (fun schema => schema.id == MaybeI32.Oria.id) ==
        some MaybeI32.Oria.schema do
    throwError "transitive object schema closure changed"
  let .ok program := candidate.checkClosure
    | throwError "object closure certificate was unavailable"
  have _ : ObjectCatalog := program.objects
  have _ : Function.Catalog := program.functions
  have _ : Oria.Command.Catalog := program.commands

run_cmd do
  let candidate ← collectSpec #[
    ⟨_, moveAndRead.ref⟩
  ]
  let some member := candidate.members.find? fun member =>
      member.definition.source == ``moveAndRead
    | throwError "command fixture was not collected"
  unless member.dependencies.commands.size == 2 &&
      member.dependencies.commands.all (fun dependency =>
        (candidate.commands.resolveRef dependency.ref).isOk) do
    throwError "stored command dependencies did not resolve"
  let .ok _ := candidate.checkClosure
    | throwError "command closure certificate was unavailable"

run_cmd do
  let candidate ← collectSpec #[
    ⟨_, absentCommand.ref⟩
  ]
  match candidate.checkClosure with
  | .error (.unknownCommand `oria.proofs.absent) => pure ()
  | _ => throwError "command preflight did not preserve the missing route key"

run_cmd do
  let bad : DeclRef leaf.signature := .named `Oria.Proofs.Collect.absent
  let entries : Array IR.DeclRef.Some := #[⟨_, bad⟩]
  match collectWithStandardCatalog (← getEnv) entries with
  | .error (.unknownMcFunction `Oria.Proofs.Collect.absent) => pure ()
  | _ => throwError "missing registry diagnostic changed"

run_cmd do
  let wrongSig : Signature := { args := [], result := .unit, grade := .pure }
  let bad : DeclRef wrongSig := .named ``leaf
  let entries : Array IR.DeclRef.Some := #[⟨_, bad⟩]
  match collectWithStandardCatalog (← getEnv) entries with
  | .error (.functionSignatureMismatch name expected actual) =>
      unless name == ``leaf && expected == wrongSig && actual == leaf.signature do
        throwError "signature mismatch did not preserve its typed target"
  | _ => throwError "signature mismatch diagnostic changed"

run_cmd do
  let wrongSig : Signature := { args := [], result := .unit, grade := .pure }
  let wrong : DeclRef wrongSig := .named ``leaf
  let entries : Array IR.DeclRef.Some := #[
    ⟨_, leaf.ref⟩,
    ⟨_, wrong⟩
  ]
  match collectWithStandardCatalog (← getEnv) entries with
  | .error (.functionSignatureMismatch name expected actual) =>
      unless name == ``leaf && expected == wrongSig && actual == leaf.signature do
        throwError "cached signature mismatch did not preserve its typed target"
  | _ => throwError "cached duplicate signature mismatch was not diagnosed"

run_cmd do
  let leftEntries := #[
    ⟨_, root.ref⟩,
    ⟨_, envelopeRoot.ref⟩
  ]
  let rightEntries := leftEntries.reverse
  let left ← collectSpec leftEntries
  let right ← collectSpec rightEntries
  unless left.members.map (·.definition.source) == right.members.map (·.definition.source) &&
      left.schemas.map (·.id) == right.schemas.map (·.id) do
    throwError "collection order depends on source entry order"

end Oria.Proofs.Collect
