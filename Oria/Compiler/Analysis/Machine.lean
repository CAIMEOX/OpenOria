module

public import Oria.IR.Machine.Program

namespace Oria.Analysis.Machine

open Oria.IR Oria.IR.Machine

/-- Stable block-local identity under extension of the instruction prefix. -/
@[expose] public def number {n : Nat} (i : Fin n) : Nat := n - 1 - i.val

@[simp] public theorem number_weaken {n : Nat} (i : Fin n) (m : Nat) :
    number (⟨m + i.val, by omega⟩ : Fin (m + n)) = number i := by
  simp only [number]
  omega

@[expose] public def use {n : Nat} (value : Atom n) : BitVec n :=
  match value with
  | .var i => BitVec.ofNat n (1 <<< i.val)
  | .lit _ => 0

/-- Substitute selected tuple components through their actual operands. -/
@[expose] public def uses {n m : Nat} (values : Vector (Atom n) m) (mask : BitVec m) : BitVec n :=
  (List.finRange m).foldl (init := 0) fun acc i =>
    if mask.getLsb i then acc ||| use (values.get i) else acc

public def edge {layout : List Nat} {n : Nat}
    (params : {m : Nat} → Scope.Var Unit layout m → BitVec m)
    (target : Edge layout n) : BitVec n :=
  uses target.values (params target.target)

public def condition {n : Nat} : Condition (Atom n) → BitVec n
  | .isTrue v => use v
  | .compare _ l r => use l ||| use r

public def exit {layout : List Nat} {r n : Nat}
    (params : {m : Nat} → Scope.Var Unit layout m → BitVec m)
    (result : BitVec r) : Terminator layout r n → BitVec n
  | .ret values => uses values result
  | .jump target => edge params target
  | .branch c yes no => condition c ||| edge params yes ||| edge params no
  | .switch value cases fallback =>
      cases.foldl (fun mask entry => mask ||| edge params entry.2)
        (use value ||| (fallback.map (edge params)).getD 0)

/-- Data dependencies of one operation, with call arities supplied by the fixed point. -/
@[expose] public def inputs
    {functions : List IR.Machine.Signature} {n m : Nat}
    (params : {sig : IR.Machine.Signature} → Scope.Var Unit functions sig → BitVec sig.args)
    (op : Op functions n m) (out : BitVec m) : BitVec n :=
  match op with
  | .division l r => use l ||| use r
  | .checkpoint _ => 0
  | .nbt _ values => values.foldl (fun mask value => mask ||| use value) 0
  | .unary _ value => if out == 0 then 0 else use value
  | .binary _ l r => if out == 0 then 0 else use l ||| use r
  | .allocate _ values => if out == 0 then 0 else uses values (BitVec.allOnes _)
  | .tag value | .project _ value => if out == 0 then 0 else use value
  | .promote _ value | .refGet _ value => use value
  | .rootGet _ => 0
  | .rootSet _ values | .refNew _ values => uses values (BitVec.allOnes _)
  | .refSet _ pointer values => use pointer ||| uses values (BitVec.allOnes _)
  | .command request =>
      request.traverseK (fun value next => use value ||| next value) (fun _ => 0)
  | .call callee values => uses values (params callee)
  | .execute scope _ callee values =>
      scope.traverseK (fun value next => use value ||| next value)
        (fun _ => uses values (params callee))

@[simp] public theorem uses_zero {n m : Nat} (values : Vector (Atom n) m) : uses values 0 = 0 := by
  simp [uses]
  generalize List.finRange m = indices
  induction indices with
  | nil => rfl
  | cons _ _ ih => exact ih

end Oria.Analysis.Machine
