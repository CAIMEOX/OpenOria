module

import Oria.Proofs.Fixtures.Envelope
import Oria.Meta.McFunction
import Lean.Elab.Command
import Oria.Meta.Quote
meta import Oria.Proofs.Fixtures.Envelope
meta import Oria.Meta.McFunction
meta import Oria.Meta.Quote

namespace Oria.Proofs.ObjectDerive

open Oria Oria.IR
open Oria.Proofs.Fixtures
open Lean Lean.Elab Lean.Elab.Command

private def checkQuotation {A : Type} [Quote A] [ToExpr A] (value : A) : Term.TermElabM Unit := do
  let expr ← Term.elabTermEnsuringType (quote value : Term) (some (toTypeExpr A))
  unless ← Lean.Meta.isDefEq expr (toExpr value) do
    throwError "quotation does not denote its input value"

run_cmd
  liftTermElabM do
    let id : TypeId := ⟨Name.str (.num `quoted 7) "δ field", []⟩
    checkQuotation id
    for code in [ObjTy.unit, .bool, .i32, .option .i32, .data id,
        .option (.option (.data id))] do
      checkQuotation code
    Lean.Meta.withLocalDeclD ``ObjTy.i32 (mkConst ``Nat) fun _ =>
      checkQuotation ObjTy.i32

example : MaybeI32.Oria.code = .data MaybeI32.Oria.id := rfl

example : Object MaybeI32 MaybeI32.Oria.code := inferInstance

example : Prog .pure MaybeI32 :=
  MaybeI32.Obj.Ctor.none

example (value : Val Int32) : Prog .pure MaybeI32 :=
  MaybeI32.Obj.Ctor.some value

example : Prog .pure Choice :=
  Choice.Obj.Ctor.rock

example : Prog .pure Naming :=
  Naming.Obj.Ctor.fooDesc

example : Prog .pure Aliased :=
  Aliased.Obj.Ctor.wrap (I32.lit 1)

example : Prog .pure Token :=
  Token.Obj.Ctor.mk

example (payload : Val MaybeI32) :
    Prog .pure Envelope :=
  Envelope.Obj.Ctor.wrap payload

@[mcfunction]
private def built (value : Val Int32) : Prog .pure MaybeI32 :=
  MaybeI32.Obj.Ctor.some value

example : built.signature =
    { args := [.i32], result := MaybeI32.Oria.code, grade := .pure } := rfl

example : DeclRef built.signature := built.ref

example : Val Int32 → Prog .pure MaybeI32 := built.call

run_cmd
  let typeName := ``Oria.Proofs.Fixtures.MaybeI32
  let some entry := ObjectRegistry.find? (← getEnv) typeName
    | throwError "derived object is absent from the imported registry"
  unless entry.declaration.name == typeName do
    throwError "imported registry contains the wrong object code"
  unless entry.objectName == `Oria.Proofs.Fixtures.MaybeI32.Oria.object do
    throwError "imported registry contains the wrong Object instance name"
  unless entry.declaration.constructors.length == 2 do
    throwError "imported registry contains the wrong constructor count"

end Oria.Proofs.ObjectDerive
