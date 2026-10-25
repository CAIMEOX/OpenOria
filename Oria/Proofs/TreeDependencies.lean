module

public meta import Oria.Meta.Elab.ProgMatch

meta import Oria.Std.Manifest

import Oria.Std.Command.Declarations
import Oria.Std.Manifest

public import Oria.IR.Tree.Dependencies
public import Oria.Proofs.Fixtures.Envelope
import Oria.Proofs.McFunctionUtil
public import Oria.Std
public import Oria.Command.Resolve
meta import Oria.Proofs.Fixtures.Envelope
public meta import Oria.IR.Tree.Dependencies
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Std
public meta import Oria.Command.Resolve

namespace Oria.Proofs.TreeDependencies

open Oria Oria.IR Oria.IR.Tree
open Lean Lean.Elab Command
open Oria.Proofs.Fixtures
open Oria.Proofs.McFunctionUtil
open Oria.Std.Command.Arg

@[mcfunction]
private def signatureOnly (_ : Val MaybeI32) : Prog (Grade.handled .pure) Unit :=
  Prog.pure Val.unit

@[mcfunction]
private def optionSignatureOnly (_ : Val (Option MaybeI32)) : Prog (Grade.handled .pure) Unit :=
  Prog.pure Val.unit

@[mcfunction]
public def callee (value : Val Int32) : Prog .pure Int32 :=
  Prog.pure value

@[mcfunction]
private def caller (value : Val Int32) : Prog .pure Int32 :=
  callee.call value

private def position (x : Val Int32) : Vec3 :=
  .world
    (.relative (.dynamic (x + 1)))
    (.absolute (.static 80))
    (.relative (.static 0))

private def teleportGrade : Grade :=
  Std.Teleport.grade .self (position (I32.lit 0))

private def teleport (x : Val Int32) : Prog teleportGrade Int32 :=
  Std.Teleport.to .self (position x)

@[mcfunction]
private def nestedCommand
    (condition : Val Bool) (x : Val Int32) :
    Prog teleportGrade Int32 :=
  Prog.bind
    (Prog.branch condition (Prog.pure x) (Prog.pure (x + 1)))
    teleport

@[mcfunction]
private def constructEnvelope (value : Val MaybeI32) : Prog .pure Envelope :=
  Envelope.Obj.Ctor.wrap value

@[mcfunction]
private def inspectEnvelope (value : Val Envelope) : Prog .pure Int32 :=
  do
    match value with
    | .wrap .none => return 0
    | .wrap (.some n) => return n

private def functionName (dependency : FunctionDependency) : Lean.Name :=
  let .named name := dependency.ref.key
  name

private def commandName (dependency : CommandDependency) : Lean.Name :=
  dependency.ref.key

run_cmd do
  let signature ← elaborate ``signatureOnly
  let option ← elaborate ``optionSignatureOnly
  unless signature.definition.dependencies.objectTypes.contains MaybeI32.Oria.id &&
      option.definition.dependencies.objectTypes.contains MaybeI32.Oria.id do
    throwError "signature object dependencies were not observed"

run_cmd do
  let caller ← elaborate ``caller
  let dependencies := caller.definition.dependencies.functions
  let some dependency := dependencies[0]?
    | throwError "direct call dependency is absent"
  unless dependencies.size == 1 && functionName dependency == ``callee &&
      dependency.sig == callee.signature do
    throwError "direct call dependency changed"

run_cmd do
  let command ← elaborate ``nestedCommand
  let dependencies := command.definition.dependencies.commands
  let some dependency := dependencies[0]?
    | throwError "nested command dependency is absent"
  unless dependencies.size == 1 &&
      commandName dependency == Std.Command.Declarations.teleport.key &&
      dependency.sig == Std.Command.Declarations.teleport.signature do
    throwError "typed command dependency changed"
  let .ok catalog := Std.Manifest.commandCatalog
    | throwError "standard command catalogue did not build"
  unless (Datapack.Version.resolveRef .dp121 catalog dependency.ref).isOk do
    throwError "observed command reference did not resolve in DP121"

run_cmd do
  let construct ← elaborate ``constructEnvelope
  let inspect ← elaborate ``inspectEnvelope
  for dependencies in [
      construct.definition.dependencies,
      inspect.definition.dependencies
    ] do
    unless dependencies.objectTypes.contains Envelope.Oria.id &&
        dependencies.objectTypes.contains MaybeI32.Oria.id do
      throwError "constructor or case object dependencies changed"

example (left right : Dependencies) (dependency : FunctionDependency) :
    dependency ∈ (left.combine right).functions ↔
      dependency ∈ left.functions ∨ dependency ∈ right.functions :=
  Dependencies.function_mem_combine dependency

example (left right : Dependencies) (dependency : CommandDependency) :
    dependency ∈ (left.combine right).commands ↔
      dependency ∈ left.commands ∨ dependency ∈ right.commands :=
  Dependencies.command_mem_combine dependency

example (left right : Dependencies) (id : TypeId) :
    (left.combine right).objectTypes.contains id ↔
      left.objectTypes.contains id ∨ right.objectTypes.contains id :=
  Dependencies.object_mem_combine id

end Oria.Proofs.TreeDependencies
