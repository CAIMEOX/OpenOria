module

import Oria
meta import Oria

namespace Oria.Proofs.ArithmeticSyntax

open Oria Oria.Std.Command.Arg

example : I32.divide (-7) 3 = some (-3 : Int32) := by
  native_decide

example : I32.divide 7 0 = none := by
  native_decide

example : I32.divide (-2147483648) (-1) = some (-2147483648 : Int32) := by
  native_decide

private def argsTraversalNeedsNoMonad : Nat :=
  (Args.nil : Args (fun _ : ObjTy => Unit) []).traverseK
    (r := Nat)
    (fun _ next => next ())
    (fun _ => 0)

example : argsTraversalNeedsNoMonad = 0 := by
  native_decide

private def segmentTraversalNeedsNoMonad
    (segment : Oria.Command.Segment (fun _ => Unit)) : Nat :=
  segment.traverseK
    (r := Nat)
    (fun _ next => next ())
    (fun _ => 0)

example : segmentTraversalNeedsNoMonad .space = 0 := by
  native_decide

example (x y : Val Int32) : Prog .failure Int32 := (x + 1) * (y - 2) / 3
example (x y : Val Int32) : Prog .failure Int32 := (x - y) / 2

@[mcfunction]
private def quotient (x y : Val Int32) : Prog .failure Int32 := do
  let q ← x / y
  return q + 1

private structure Action where
  value : Val Int32

private instance : HAdd Action Action (Prog .pure Int32) where
  hAdd x y := Prog.pure (x.value + y.value)

@[mcfunction]
private def inferredComputation (x y : Val Int32) : Prog .pure Int32 := do
  let n ← Action.mk x + Action.mk y
  return n

@[mcfunction]
private def inferredStatement (x y : Val Int32) : Prog .pure Unit := do
  Action.mk x + Action.mk y
  return Val.unit

example (x : Val Int32) : Decimal := 1 + x
example (x : Int32) : Scalar := x + 1
example (x : Float) : Decimal := x + 0.5

end Oria.Proofs.ArithmeticSyntax
