module

import Oria.IR.Cont.Support

namespace Oria.Proofs.ContScopedSupport

open Oria Oria.IR

private def head : Cont.Atom [.i32] .i32 :=
  .local Scope.Var.head

private def old : Cont.Atom [.bool, .i32] .i32 :=
  head.weaken .bool

/-- Support membership follows typed lexical positions through weakening. -/
theorem weakened_atom_uses_old_position :
    old.support.Contains
      ((Scope.Var.head : Scope.Var Unit [ObjTy.i32] .i32).weaken .bool) := by
  simp [old, head, Cont.Atom.weaken, Cont.Atom.rename, Cont.Atom.support,
    Cont.Support.Contains, Cont.Support.singleton]

private def ignoresResult : Cont.Comp [.i32] .i32 [] :=
  Cont.Comp.letOp
    (.copy (.local Scope.Var.head))
    (Cont.Comp.ret (.i32 7))

/-- A structurally unused `letOp` result is absent from its continuation mask. -/
theorem let_result_is_unused :
    (Cont.Comp.ret (.i32 7) : Cont.Comp [.i32, .i32] .i32 []).Unused Scope.Var.head := by
  simp [Cont.Comp.Unused, Cont.Comp.Uses,
    Cont.Atom.support, Cont.Support.Contains, Cont.Support.empty]

private abbrev Γ : List ObjTy := [.i32, .i32]

private def sig : List ObjTy := .i32 :: Γ

private def captures : Args (Cont.Atom Γ) Γ :=
  (Scope.Var.identity Unit Γ).map Cont.Atom.local

private def jump : Cont.Comp Γ .i32 [sig] :=
  Cont.Comp.jump
    (Scope.Var.head : Scope.Var Unit [sig] sig)
    (.cons (.i32 3) captures)

/-- The first explicit join capture contributes its exact lexical position. -/
theorem jump_uses_first_capture :
    jump.support.Contains (Scope.Var.head : Scope.Var Unit Γ .i32) := by
  unfold jump sig
  rw [Cont.Comp.support_jump]
  simp [captures, Cont.supportArgs, Cont.Atom.support,
    Cont.Support.Contains, Cont.Support.singleton, Cont.Support.combine,
    Cont.Support.empty, Scope.Var.identity, Args.tabulate, Args.map]
  exact Or.inl (Fin.ext (by simp))

/-- A same-shaped later capture remains distinct by lexical position. -/
theorem jump_uses_second_capture :
    jump.support.Contains
      ((Scope.Var.head : Scope.Var Unit [ObjTy.i32] .i32).weaken .i32) := by
  unfold jump sig
  rw [Cont.Comp.support_jump]
  simp [captures, Cont.supportArgs, Cont.Atom.support,
    Cont.Support.Contains, Cont.Support.singleton, Cont.Support.combine,
    Cont.Support.empty, Scope.Var.identity, Args.tabulate, Args.map]
  exact Or.inr (Fin.ext (by simp))

private abbrev Outer : List ObjTy := [.i32]

private def literalCaptureBody :
    Cont.Comp (.i32 :: Outer) .i32 [] :=
  Cont.Comp.ret <| .local <|
    (Scope.Var.head : Scope.Var Unit Outer .i32).weaken .i32

private def literalCaptureProgram : Cont.Comp Outer .i32 [] :=
  let sig : List ObjTy := .i32 :: Outer
  let join : Scope.Var Unit [sig] sig := Scope.Var.head
  Cont.Comp.letJoin literalCaptureBody <|
    Cont.Comp.jump join (.cons (.i32 0) (.cons (.i32 7) .nil))

/- Definition-site support is determined by explicit jump arguments. -/
theorem literal_capture_uses_no_outer_local :
    literalCaptureProgram.Unused
      (Scope.Var.head : Scope.Var Unit Outer .i32) := by
  simp [literalCaptureProgram, literalCaptureBody, Cont.Comp.Unused,
    Cont.Comp.Uses, Cont.supportArgs, Cont.Atom.support,
    Cont.Support.Contains, Cont.Support.combine, Cont.Support.empty]

end Oria.Proofs.ContScopedSupport
