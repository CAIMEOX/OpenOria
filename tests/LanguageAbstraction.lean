module

import Oria
meta import Oria

open Oria

set_option linter.unusedVariables false

example {A : Type} {a : ObjTy} [Object A a] (v : Val A) : True := by
  fail_if_success
    have : Val A .persistent := by cases v; constructor; assumption
  fail_if_success
    have : IR.Tree.Expr a := by cases v; assumption
  fail_if_success
    have : IR.Tree.Expr a := by cases v; rename_i x; cases x
  fail_if_success
    have : IR.Tree.Expr a := Oria.Val.expr v
  trivial

example {A : Type} {a : ObjTy} [Object A a] {g : Grade} (v : Prog g A) : True := by
  fail_if_success
    have : Prog g A .persistent := by cases v; constructor; assumption
  fail_if_success
    have : IR.Tree.Build (IR.Tree.Tree g a) := by cases v; assumption
  trivial

example (v : EncodedVal .i32) : True := by
  fail_if_success
    have : IR.Tree.Expr .i32 := by cases v; assumption
  trivial

example (recipe : McFunction.Internal.Recipe) : True := by
  fail_if_success
    have : ElaboratedDef := by cases recipe; assumption
  trivial

example [fn : BuildFn (Val Int32 → Prog .pure Int32) ⟨[.i32], .i32, .pure⟩] : True := by
  fail_if_success
    have : (Val Int32 → Prog .pure Int32) →
        Args IR.Tree.Expr [.i32] → IR.Tree.Build (IR.Tree.Tree .pure .i32) := by
      cases fn
      assumption
  trivial

example : True := by
  fail_if_success
    have : Object String .i32 := by constructor; trivial
  fail_if_success
    have : Object String .i32 := by
      have object : Object Int32 .i32 := inferInstance
      cases object
      constructor
      assumption
  fail_if_success
    have : Object String .i32 := Oria.makeObject
  trivial

example (p : Nbt.Access (Val Int32) (Array Int32) (Array Int32)) : True := by
  fail_if_success
    have : Nbt.Access (Val Int32) (Array Int32) Int32 := by
      cases p
      constructor
      assumption
  trivial

example (global : Nbt.Global Int32) : True := by
  fail_if_success
    have : Nbt.Global Bool := by cases global; constructor; assumption
  fail_if_success
    have : Nbt.Global Int32 := by
      constructor
      constructor
  trivial

example (decl : IR.Nbt.GlobalDecl) : True := by
  fail_if_success
    have : IR.Nbt.GlobalRef × Nbt.Any := by cases decl; assumption
  fail_if_success
    have : IR.Nbt.GlobalDecl := by constructor; constructor
  trivial

@[mcfunction]
private def identity {r : Region} (x : Val Int32 r) : Prog .pure Int32 r :=
  Prog.pure x

@[mcfunction]
private def explicitPromotion : Prog Persistent.allocGrade Int32 .persistent := do
  let x ← Persistent.persist 37
  identity.call x
