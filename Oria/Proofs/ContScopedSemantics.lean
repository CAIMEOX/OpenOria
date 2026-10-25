module

import Oria.IR.Cont.Semantics

namespace Oria.Proofs.ContScopedSemantics

open Oria Oria.IR
open Oria.Semantics.Cont

private def env : Env [.i32, .i32] :=
  .cons (.i32 11) (.cons (.i32 29) .nil)

/-- Repeated object types remain distinguishable by lexical position at evaluation. -/
theorem repeated_type_lookup :
    atom env (.local Scope.Var.head) = .i32 11 ∧
      atom env (.local
        ((Scope.Var.head : Scope.Var Unit [ObjTy.i32] .i32).weaken .i32)) = .i32 29 := by
  simp [env, Env.lookup]

private def model : Model Unit :=
  { unary := fun _ _ => pure .failed
    binary := fun _ _ _ => pure .failed
    construct := fun _ _ => pure .failed
    call := fun _ _ => pure .failed
    command := fun _ => pure .failed
    execute := fun _ _ _ => pure .failed
    memory := fun _ _ => pure .failed
    project := fun _ _ => pure none }

private def copyHead : IR.Cont.Comp [.i32] .i32 [] :=
  IR.Cont.Comp.letOp
    (.copy (.local Scope.Var.head))
    (IR.Cont.Comp.ret (.local Scope.Var.head))

/-- `letOp` extends the value telescope at its typed head. -/
theorem eval_copy_head :
    Id.run (eval model 2 (.cons (.i32 7) .nil) .nil copyHead).run () =
      (some (.returned (.i32 7)), ()) := by
  unfold copyHead
  rw [eval_letOp]
  simp [evalOp, Env.lookup, Env.extend]
  change (some (Result.returned (.i32 7)), ()) =
    (some (Result.returned (.i32 7)), ())
  rfl

private def optionCase : IR.Cont.Comp [.option .i32]
    .i32 [] :=
  .switch (.local Scope.Var.head)
    (.cons .none (.ret (.i32 0)) (.cons .some (.ret (.local Scope.Var.head)) .nil))

/-- The `some` arm receives its payload at the typed lexical head. -/
theorem eval_option_payload :
    Id.run (eval model 4 (.cons (.some (.i32 13)) .nil) .nil optionCase).run () =
      (some (.returned (.i32 13)), ()) := by
  unfold optionCase
  simp [eval, evalArms, project, atom, Env.lookup, Args.append]
  change (some (Result.returned (.i32 13)), ()) =
    (some (Result.returned (.i32 13)), ())
  rfl

private abbrev Γ : List ObjTy := [.i32]

private def capturedSig : List ObjTy := .i32 :: Γ

private def capturedBody : IR.Cont.Comp (.i32 :: Γ) .i32 [] :=
  IR.Cont.Comp.ret <| .local <|
    (Scope.Var.head : Scope.Var Unit Γ .i32).weaken .i32

private def capturedProgram : IR.Cont.Comp Γ .i32 [] :=
  let join : Scope.Var Unit [capturedSig] capturedSig := Scope.Var.head
  let captures : Args (IR.Cont.Atom Γ) Γ :=
    .cons (.i32 7) .nil
  IR.Cont.Comp.letJoin capturedBody <|
    IR.Cont.Comp.jump join (.cons (.i32 0) captures)

/-- A join body observes the explicit capture tuple transferred by its jump. -/
theorem eval_explicit_capture :
    Id.run (eval model 3 (.cons (.i32 41) .nil) .nil capturedProgram).run () =
      (some (.returned (.i32 7)), ()) := by
  unfold capturedProgram capturedSig
  rw [eval_letJoin, eval_jump]
  rw [Scope.Var.lookup_head]
  simp [capturedBody, atom, Env.lookup, evalArgs, Args.map]
  change (some (Result.returned (.i32 7)), ()) =
    (some (Result.returned (.i32 7)), ())
  rfl

private def memoryRoot : RootRef .i32 :=
  ⟨`fixture.memoryRoot⟩

private def memoryModel : Model Int32 :=
  { unary := fun _ _ => pure .failed
    binary := fun _ _ _ => pure .failed
    construct := fun _ _ => pure .failed
    call := fun _ _ => pure .failed
    command := fun _ => pure .failed
    execute := fun _ _ _ => pure .failed
    project := fun _ _ => pure none
    memory := fun
      | .rootGet (a := .i32) _ => fun _ => do
          let value ← get
          pure (.returned (.i32 value))
      | .rootSet (a := .i32) _ => fun arguments => do
          match arguments with
          | .cons (.i32 value) .nil =>
              set value
              pure (.returned .unit)
      | _ => fun _ => pure .failed }

private def rootSetThenGet : IR.Cont.Comp [] .i32 [] :=
  .letOp (.memory (.rootSet memoryRoot) (.cons (.i32 23) .nil)) <|
    .letOp (.memory (.rootGet memoryRoot) .nil) <|
      .ret (.local Scope.Var.head)

/-- A root write is visible to a subsequent root read in the threaded model state. -/
theorem eval_root_set_then_get :
    Id.run (eval memoryModel 3 .nil .nil rootSetThenGet).run 0 =
      (some (.returned (.i32 23)), 23) := by
  simp [eval, evalOp, memoryModel, rootSetThenGet, atom, Env.extend, Env.lookup]
  change (some (Result.returned (.i32 23)), 23) =
    (some (Result.returned (.i32 23)), 23)
  rfl

end Oria.Proofs.ContScopedSemantics
