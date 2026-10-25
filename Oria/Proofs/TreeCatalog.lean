module

public meta import Oria.Meta.Elab.ProgMatch

import Oria.IR.Catalog.Object
meta import Oria.IR.Catalog.Object

import Oria.Proofs.Fixtures.Envelope
import Oria.IR.Tree.Definition
import Oria.Proofs.McFunctionUtil
meta import Oria.Proofs.Fixtures.Envelope
meta import Oria.Proofs.McFunctionUtil

namespace Oria.Proofs.TreeCatalog

open Oria Oria.IR
open Oria.Proofs.Fixtures
open Oria.Proofs.McFunctionUtil
open Lean Lean.Elab Command

#guard (ObjectCatalog.build [MaybeI32.Oria.schema, Envelope.Oria.schema]).isOk

#guard
  match ObjectCatalog.build [Envelope.Oria.schema] with
  | .error (.unresolvedObjectType owner missing) =>
      owner == Envelope.Oria.id && missing == MaybeI32.Oria.id
  | _ => false

#guard
  match ObjectCatalog.build [MaybeI32.Oria.schema, MaybeI32.Oria.schema] with
  | .error (.duplicateObjectType id) => id == MaybeI32.Oria.id
  | _ => false

@[mcfunction]
private def validConstructor (value : Val Int32) : Prog .pure MaybeI32 :=
  MaybeI32.Obj.Ctor.some value

run_cmd
  let definition := (← elaborate ``validConstructor).definition
  let catalog ←
    match ObjectCatalog.build [MaybeI32.Oria.schema] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build object catalog: {repr diagnostic}"
  unless (catalog.link definition).isOk do
    throwError "failed to link a valid Tree constructor"

private def missingConstructorRef : CtorRef MaybeI32.Oria.id [] :=
  ⟨`Oria.Proofs.Fixtures.MaybeI32.missing⟩

private def missingConstructor : IR.Tree.Def
    { args := [], result := .data MaybeI32.Oria.id, grade := .pure } :=
  .build fun | .nil => pure (.perform (.construct (.data missingConstructorRef) .nil))

run_cmd
  let definition := missingConstructor
  let catalog ←
    match ObjectCatalog.build [MaybeI32.Oria.schema] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build object catalog: {repr diagnostic}"
  match catalog.link definition with
  | .error (.unknownConstructor owner name) =>
      unless owner == MaybeI32.Oria.id && name == missingConstructorRef.name do
        throwError "unknown-constructor diagnostic contained the wrong identity"
  | .error diagnostic =>
      throwError "expected unknown-constructor diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "missing Tree constructor unexpectedly linked"

private def wrongShapeRef : CtorRef MaybeI32.Oria.id [] :=
  ⟨`Oria.Proofs.Fixtures.MaybeI32.some⟩

private def wrongShapeConstructor : IR.Tree.Def
    { args := [], result := .data MaybeI32.Oria.id, grade := .pure } :=
  .build fun | .nil => pure (.perform (.construct (.data wrongShapeRef) .nil))

run_cmd
  let definition := wrongShapeConstructor
  let catalog ←
    match ObjectCatalog.build [MaybeI32.Oria.schema] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build object catalog: {repr diagnostic}"
  match catalog.link definition with
  | .error (.constructorShapeMismatch owner name expected actual) =>
      unless owner == MaybeI32.Oria.id && name == wrongShapeRef.name &&
          expected == [.i32] && actual == [] do
        throwError "constructor-shape diagnostic contained the wrong telescope"
  | .error diagnostic =>
      throwError "expected constructor-shape diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "wrong-shape Tree constructor unexpectedly linked"

run_cmd
  let definition := (← elaborate ``validConstructor).definition
  let catalog ←
    match ObjectCatalog.build [] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build empty object catalog: {repr diagnostic}"
  match catalog.link definition with
  | .error (.unknownObjectType id) =>
      unless id == MaybeI32.Oria.id do
        throwError "unknown-type diagnostic contained the wrong identity"
  | .error diagnostic =>
      throwError "expected unknown-type diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "Tree with an absent result type unexpectedly linked"

@[mcfunction]
private def validCase (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0
    | .some payload => return payload

run_cmd
  let definition := (← elaborate ``validCase).definition
  let catalog ←
    match ObjectCatalog.build [MaybeI32.Oria.schema] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build object catalog: {repr diagnostic}"
  unless (catalog.link definition).isOk do
    throwError "failed to link a valid exhaustive Tree case"

@[mcfunction]
private def incompleteCase (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0

run_cmd
  let definition := (← elaborate ``incompleteCase).definition
  let catalog ←
    match ObjectCatalog.build [MaybeI32.Oria.schema] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build object catalog: {repr diagnostic}"
  unless (catalog.link definition).isOk do
    throwError "a pattern matrix with closed constructor references failed object linking"

@[mcfunction]
private def callTarget (value : Val MaybeI32) : Prog .pure MaybeI32 :=
  Prog.pure value

@[mcfunction]
private def callOverClosedTypes (value : Val MaybeI32) : Prog .pure MaybeI32 :=
  callTarget.call value

run_cmd
  let definition := (← elaborate ``callOverClosedTypes).definition
  let .ok catalog := ObjectCatalog.build [MaybeI32.Oria.schema]
    | throwError "failed to build object catalog"
  unless (catalog.link definition).isOk do
    throwError "failed to link a function call over closed object types"

private def absentId : TypeId :=
  ⟨`Oria.Proofs.TreeCatalog.Absent, []⟩

private def badCallSig : Signature :=
  { args := [], result := .data absentId, grade := .pure }

private def badCallRef : DeclRef badCallSig :=
  .named `Oria.Proofs.TreeCatalog.BadSignature

private def primitiveCallerSig : Signature :=
  { args := [], result := .unit, grade := .pure }

private def badCallDefinition : IR.Tree.Def primitiveCallerSig :=
  IR.Tree.Def.build fun
    | .nil =>
        IR.Tree.Build.bind (.perform (.call badCallRef .nil)) fun _ =>
          pure (.ret .unit)

#guard
  match ObjectCatalog.build [] with
  | .error _ => false
  | .ok catalog =>
      match catalog.link badCallDefinition with
      | .error (.unknownObjectType id) => id == absentId
      | _ => false

end Oria.Proofs.TreeCatalog
