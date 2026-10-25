module

import Oria.Std.Command.Declarations

public import Oria.Std.DP121
public import Oria.Std
public meta import Oria.Std.DP121

open Oria.Command (Objective ScoreOp)

namespace Oria.Proofs.DP121Plan

open Oria Oria.Command Oria.Target.DP121
open Oria.Std.Command.Arg

private inductive PieceView where
  | token : String → PieceView
  | space : PieceView
  | i32 : Int32 → PieceView
  | literal : String → PieceView
  | hole : Nat → PieceView
  deriving BEq, DecidableEq, Repr

private def view {v : ObjTy → Type} : CommandPiece v → PieceView
  | .token value => .token value.text
  | .space => .space
  | .i32 value => .i32 value
  | .literal value => .literal (value.format.pretty 120)
  | .hole h => .hole h.parameter.index

private def views {v : ObjTy → Type} {sig : Command.Signature}
    (plan : CommandPlan v sig) : Array PieceView :=
  plan.pieces.map view

private def teleportRequest (position : Vec3) :=
  Std.Command.Declarations.teleport.call <|
    .cons (Command.encode (.self : Target)) <| .cons (Command.encode position) .nil

private def staticTeleport := teleportRequest <| .world
  (.absolute (.static 1)) (.absolute (.static 2)) (.absolute (.static 3))

private def mixedTeleport (x : Val Int32) := teleportRequest <| .world
  (.absolute (.dynamic x)) (.absolute (.static 2)) (.absolute (.static 3))

private def dynamicTeleport (x y z : Val Int32) := teleportRequest <| .world
  (.absolute (.dynamic x)) (.absolute (.dynamic y)) (.absolute (.dynamic z))

#guard match Oria.Std.DP121.plan staticTeleport with
  | .ok planned => views planned == #[
      .token "teleport", .space, .token "@s", .space,
      .i32 1, .space, .i32 2, .space, .i32 3]
  | .error _ => false

#guard match Oria.Std.DP121.plan (mixedTeleport (I32.lit 7)) with
  | .ok planned => views planned == #[
      .token "teleport", .space, .token "@s", .space,
      .hole 0, .space, .i32 2, .space, .i32 3]
  | .error _ => false

#guard match Oria.Std.DP121.plan
    (dynamicTeleport (I32.lit 1) (I32.lit 2) (I32.lit 3)) with
  | .ok planned =>
      (views planned).filterMap (fun piece => match piece with
        | .hole index => some index | _ => none) == #[0, 1, 2]
  | .error _ => false

private def objective : Objective := .ofToken (.ofString "oria.points")
private def slot (holder : ScoreHolder) : ScoreSlot := ⟨holder, objective⟩
private def operationRequest := Std.Command.Declarations.scoreOperation.call <|
  .cons (Command.encode (slot .self)) <| .cons (Command.encode (.add : ScoreOp)) <|
    .cons (Command.encode (slot (.named (.ofString "source")))) .nil

#guard match Oria.Std.DP121.plan operationRequest with
  | .ok planned =>
      planned.resolved.ref.key == Oria.Std.Command.Declarations.scoreOperation.key &&
      (views planned).contains (.token "+=")
  | .error _ => false

#guard match Oria.Std.DP121.plan staticTeleport with
  | .ok planned =>
      planned.requirements == staticTeleport.requirements
  | .error _ => false

private def teleportOnlyCatalog : Except Diagnostic Command.Catalog :=
  Command.Catalog.build [Std.Command.Declarations.teleport.declaration]

#guard match teleportOnlyCatalog with
  | .ok catalog => match Oria.Target.DP121.planWithCatalog catalog staticTeleport with
    | .ok _ => true
    | .error _ => false
  | .error _ => false

#guard match teleportOnlyCatalog with
  | .ok catalog => match Oria.Target.DP121.planWithCatalog catalog operationRequest with
    | .ok _ => false
    | .error _ => true
  | .error _ => false

example {sig : Command.Signature} (planned : CommandPlan EncodedVal sig) :
    planned.mapK (fun value => value) = planned :=
  planned.mapK_id

private inductive Box (a : ObjTy) where
  | wrap : EncodedVal a → Box a

private def Box.unwrap {a : ObjTy} : Box a → EncodedVal a
  | .wrap value => value

example {sig : Command.Signature} (planned : CommandPlan EncodedVal sig) :
    (planned.mapK Box.wrap).mapK Box.unwrap = planned := by
  rw [CommandPlan.mapK_comp]
  simp [Box.unwrap]

example {sig : Command.Signature} (planned : CommandPlan EncodedVal sig) :
    planned.traverseK (fun value next => next (Box.wrap value)) fun transformed =>
      transformed.shapes = planned.shapes ∧
        transformed.resolved = planned.resolved ∧
        transformed.requirements = planned.requirements := by
  rw [CommandPlan.traverseK_pure]
  simp

example {sig : Command.Signature} (planned : CommandPlan EncodedVal sig) :
    planned.withInvocation
      (fun invocation =>
        invocation.resolved = planned.resolved ∧ invocation.parameterCount = 0)
      (fun schema _nonempty _sources invocation _complete =>
        invocation.resolved = planned.resolved ∧
          invocation.parameterCount = schema.fields.length ∧
          0 < invocation.parameterCount) := by
  exact planned.withInvocation_certified

example {sig : Command.Signature} (planned : CommandPlan EncodedVal sig) :
    planned.withInvocation
      (fun invocation => invocation.parameterCount = 0)
      (fun schema _nonempty _sources invocation _complete =>
        invocation.parameterCount = schema.fields.length) := by
  exact planned.withInvocation_coverage

example {v : ObjTy → Type}
    (schema : MacroSchema)
    (sources : InvocationSources v schema)
    (position : Fin schema.fields.length) :
    v (schema.fields.get position).ty :=
  sources.get position

example {sig : Command.Signature}
    (schema : MacroSchema)
    (invocation : Invocation (.macro schema) sig)
    (nonempty : 0 < schema.fields.length)
    (complete : invocation.parameterCount = schema.fields.length) :
    0 < invocation.parameterCount := by
  rw [complete]
  exact nonempty

private def invocationArity {v : ObjTy → Type} {sig : Command.Signature}
    (planned : CommandPlan v sig) : Nat × Nat :=
  planned.withInvocation
    (fun invocation => (0, invocation.parameterCount))
    (fun schema _nonempty _sources invocation _complete =>
      (schema.fields.length, invocation.parameterCount))

private def hasInvocationArity {v : ObjTy → Type} {sig : Command.Signature}
    (planned : Except Diagnostic (CommandPlan v sig))
    (expected : Nat × Nat) : Bool :=
  match planned with
  | .ok value => invocationArity value == expected
  | .error _ => false

example : hasInvocationArity
    (Oria.Std.DP121.plan staticTeleport) (0, 0) = true := by
  native_decide

example : hasInvocationArity
    (Oria.Std.DP121.plan (mixedTeleport (I32.lit 7))) (1, 1) = true := by
  native_decide

example : hasInvocationArity
    (Oria.Std.DP121.plan
      (dynamicTeleport (I32.lit 1) (I32.lit 2) (I32.lit 3))) (3, 3) = true := by
  native_decide

private def outsideSig : Command.Signature :=
  { schema := []
    req := Req.none
    eff := Eff.none }

private def outside : Call EncodedVal outsideSig :=
  { ref := ⟨`proof.outside.dp121, { parts := [.token (.ofString "outside")] }, none⟩
    args := .nil }

#guard match Oria.Std.DP121.plan outside with
  | .error (.unknownCommand `proof.outside.dp121) => true
  | _ => false

end Oria.Proofs.DP121Plan
