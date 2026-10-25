module

import Oria.IR.Cont.Syntax

namespace Oria.Proofs.ContScopedSyntax

open Oria Oria.IR

private def headAtom : Cont.Atom [.i32] .i32 :=
  .local Scope.Var.head

private def renamedHead : Cont.Atom [.bool, .i32] .i32 :=
  headAtom.rename
    ((Scope.Renaming.id Unit [ObjTy.i32]).weaken ObjTy.bool)

private def weakenedHead : Cont.Atom [.bool, .i32] .i32 :=
  headAtom.weaken .bool

private def weakenedManyHead : Cont.Atom [.unit, .bool, .i32] .i32 :=
  headAtom.weakenMany [.unit, .bool]

private def underBool :
    Scope.Renaming Unit Unit [ObjTy.i32] [ObjTy.bool, ObjTy.i32] :=
  (Scope.Renaming.id Unit [ObjTy.i32]).weaken ObjTy.bool

private def underUnit :
    Scope.Renaming Unit Unit
      [ObjTy.bool, ObjTy.i32] [ObjTy.unit, ObjTy.bool, ObjTy.i32] :=
  (Scope.Renaming.id Unit [ObjTy.bool, ObjTy.i32]).weaken ObjTy.unit

/-- Atom renaming exposes identity and composition as reusable laws. -/
theorem atom_rename_laws :
    headAtom.rename (Scope.Renaming.id Unit [ObjTy.i32]) = headAtom ∧
      (headAtom.rename underBool).rename underUnit =
        headAtom.rename (underUnit.comp underBool) := by
  simp

private def commandSlot : Command.SlotKey :=
  ⟨`Oria.Proofs.ContScopedSyntax.commandSlot⟩

private def commandRoute : Command.Signature :=
  { schema := [commandSlot]
    req := Req.none
    eff := Eff.none }

private def commandTemplate : Command.Template [commandSlot] :=
  { parts := [.slot ⟨0, by simp⟩] }

private def commandRef : Command.Ref commandRoute :=
  { key := `Oria.Proofs.ContScopedSyntax.command
    template := commandTemplate }

private def commandRequest :
    Command.Call (Cont.Atom [ObjTy.i32]) commandRoute :=
  { ref := commandRef
    args := .cons
      ⟨Command.Fragment.hole .i32 headAtom⟩
      .nil }

private def commandOp :
    Cont.Op [ObjTy.i32] commandRequest.grade .i32 :=
  .command commandRequest

/-- Operation composition traverses a command's dynamic holes. -/
theorem command_hole_rename_laws :
    commandOp.rename (Scope.Renaming.id Unit [ObjTy.i32]) = commandOp ∧
      (commandOp.rename underBool).rename underUnit =
        commandOp.rename (underUnit.comp underBool) := by
  simp

/-- A `letOp` result is available at the head of its continuation context. -/
private def letOpScope : Cont.Comp [.i32] .i32 [] :=
  Cont.Comp.letOp
    (.copy headAtom)
    (Cont.Comp.ret (.local Scope.Var.head))

/-- Only the `some` continuation receives the Option payload binder. -/
private def optionPayload : Cont.Comp [.option .i32] .i32 [] :=
  .switch (.local Scope.Var.head)
    (.cons .none (.ret (.i32 0))
      (.cons .some (.ret (.local Scope.Var.head)) .nil))

private def pairOwner : TypeId :=
  ⟨`Oria.Proofs.ContScopedSyntax.Pair, []⟩

private def pairConstructor : CtorRef pairOwner [.i32, .bool] :=
  ⟨`Oria.Proofs.ContScopedSyntax.Pair.pair⟩

private abbrev PairContext : List ObjTy :=
  [.data pairOwner, .i32]

private abbrev PairArmContext : List ObjTy :=
  [.i32, .bool] ++ PairContext

private def firstField : Cont.Atom PairArmContext .i32 :=
  .local Scope.Var.head

private def secondField : Cont.Atom PairArmContext .bool :=
  .local <|
    (Scope.Var.head :
      Scope.Var Unit ([ObjTy.bool] ++ PairContext) ObjTy.bool).weaken ObjTy.i32

private def pairOuter : Cont.Atom PairArmContext .i32 :=
  .local <|
    ((Scope.Var.head : Scope.Var Unit [ObjTy.i32] ObjTy.i32).weaken
      (ObjTy.data pairOwner)).weakenMany [ObjTy.i32, ObjTy.bool]

/-- Constructor fields extend the ambient context in declaration order. -/
private def multiFieldCase : Cont.Comp PairContext .i32 [] :=
  .switch (.local Scope.Var.head)
    (.cons (.data pairConstructor)
      (.branch secondField (.ret firstField) (.ret pairOuter)) .nil)

private abbrev CaptureContext : List ObjTy :=
  [.bool, .i32]

private def sharedSig : List ObjTy := .i32 :: CaptureContext

private def sharedBody :
    Cont.Comp (.i32 :: CaptureContext) .i32 [] :=
  Cont.Comp.ret (.local Scope.Var.head)

private def ambientI32 : Cont.Atom CaptureContext .i32 :=
  .local <|
    (Scope.Var.head : Scope.Var Unit [ObjTy.i32] ObjTy.i32).weaken ObjTy.bool

private abbrev DeepCaptureContext : List ObjTy :=
  .i32 :: CaptureContext

private def capturesInDefinitionOrder :
    Args (Cont.Atom DeepCaptureContext) CaptureContext :=
  (Scope.Var.identity Unit CaptureContext).map fun x =>
    Cont.Atom.local (x.weaken ObjTy.i32)

private def jumpFromDeeperContext :
    Cont.Comp CaptureContext .i32 [sharedSig] :=
  Cont.Comp.letOp
    (.copy ambientI32)
    (Cont.Comp.jump
      (Scope.Var.head : Scope.Var Unit [sharedSig] sharedSig)
      (.cons (.local Scope.Var.head) capturesInDefinitionOrder))

/-- A join call transfers every ambient capture explicitly and in definition order. -/
private def scopedJoin :
    Cont.Comp CaptureContext .i32 [] :=
  Cont.Comp.letJoin sharedBody jumpFromDeeperContext

private def outerSig : List ObjTy := [.i32]

private def innerSig : List ObjTy := [.bool]

private def outerBelowInner :
    Scope.Var Unit [innerSig, outerSig] outerSig :=
  (Scope.Var.head : Scope.Var Unit [outerSig] outerSig).weaken innerSig

/-- Nested join membership selects the older join beneath the newest one. -/
private def nestedJoin : Cont.Comp [] .i32 [] :=
  Cont.Comp.letJoin
    (Cont.Comp.ret (.local Scope.Var.head))
    (Cont.Comp.letJoin
      (Cont.Comp.ret (.i32 0))
      (Cont.Comp.jump outerBelowInner (.cons (.i32 7) .nil)))

end Oria.Proofs.ContScopedSyntax
