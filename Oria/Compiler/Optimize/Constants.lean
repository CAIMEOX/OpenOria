module

public import Oria.IR.Machine.Program
import Oria.Compiler.Optimize.ControlFlow
import Oria.Compiler.Optimize.Scalar
import Std.Data.DHashMap.Basic

namespace Oria.Optimize.Constants

open Oria.IR Oria.IR.Machine

/- Lean's LCNF folder consumes Lean expressions and declaration identities. This pass
uses Oria's scoped operand operations, Std's dependent map, and scoreboard I32 semantics.
Reachable edges contribute to a flat constant lattice; memory and calls stay opaque. -/
private inductive Value where
  | pending
  | constant : Int32 → Value
  | unknown
  deriving BEq, DecidableEq

private def Value.join : Value → Value → Value
  | .pending, b => b
  | a, .pending => a
  | .constant a, .constant b => if a == b then .constant a else .unknown
  | _, _ => .unknown

private def Value.holds : Value → Int32 → Prop
  | .pending, _ => False
  | .constant a, b => a = b
  | .unknown, _ => True

private theorem join_holds (a b : Value) (v : Int32)
    (h : a.holds v ∨ b.holds v) : (a.join b).holds v := by
  cases a <;> cases b <;> simp_all [Value.join, Value.holds]
  rename_i a b
  by_cases same : a = b <;> simp_all

private def Value.map (f : Int32 → Int32) : Value → Value
  | .pending => .pending
  | .constant a => .constant (f a)
  | .unknown => .unknown

private def Value.map₂ (f : Int32 → Int32 → Int32) : Value → Value → Value
  | .pending, _ | _, .pending => .pending
  | .constant a, .constant b => .constant (f a b)
  | _, _ => .unknown

private theorem map_holds (f : Int32 → Int32) (a : Value) (v : Int32)
    (h : a.holds v) : (a.map f).holds (f v) := by
  cases a <;> simp_all [Value.map, Value.holds]

private theorem map₂_holds (f : Int32 → Int32 → Int32) (a b : Value) (v w : Int32)
    (h : a.holds v) (k : b.holds w) : (a.map₂ f b).holds (f v w) := by
  cases a <;> cases b <;> simp_all [Value.map₂, Value.holds]

private abbrev Values (n : Nat) := Vector Value n
private abbrev Info (l : List Nat) := Std.DHashMap (Fin l.length) (fun i => Values (l.get i))

open Scalar (word binary)

private def atom {n : Nat} (vs : Values n) : Atom n → Value
  | .lit v => .constant v
  | .var i => vs[i]

private def replace {n : Nat} (vs : Values n) (a : Atom n) : Atom n :=
  match atom vs a with
  | .constant v => .lit v
  | _ => a

private def outputs {f : List Machine.Signature} {n m : Nat} (vs : Values n) : Op f n m → Values m
  | .unary .neg v => #v[(atom vs v).map (- ·)]
  | .unary .not v => #v[(atom vs v).map (fun n => word (n == 0))]
  | .binary op l r => #v[(atom vs l).map₂ (binary op) (atom vs r)]
  | .division l r =>
      let left := atom vs l
      let right := atom vs r
      let success := right.map (fun n => word (n != 0))
      let quotient := match left, right with
        | .constant x, .constant y => (Oria.I32.divide x y).map Value.constant |>.getD .unknown
        | .pending, _ | _, .pending => .pending
        | _, _ => .unknown
      #v[success, quotient]
  | _ => Vector.replicate _ .unknown

private def condition {n : Nat} (vs : Values n) : Condition (Atom n) → Value
  | .isTrue v => (atom vs v).map (fun n => word (n == 1))
  | .compare op l r => (atom vs l).map₂ (fun a b => word (Condition.test op a b)) (atom vs r)

private def send {l : List Nat} {n : Nat} (vs : Values n) (e : Edge l n) : StateM (Info l) Unit := do
  let incoming := e.target.typeCorrect.symm ▸ e.values.map (atom vs)
  modify fun info => info.insert e.target.index
    (match info.get? e.target.index with
    | none => incoming
    | some old => old.zipWith Value.join incoming)

private def propagate {l : List Nat} {r n : Nat} (vs : Values n) :
    Terminator l r n → StateM (Info l) Unit
  | .ret _ => pure ()
  | .jump e => send vs e
  | .branch c yes no =>
      match condition vs c with
      | .pending => pure ()
      | .constant v => send vs (if v == 1 then yes else no)
      | .unknown => do send vs yes; send vs no
  | .switch a cases fallback =>
      match atom vs a with
      | .pending => pure ()
      | .constant v => do
          if let some e := (cases.find? (fun c => c.1 == v)).map (·.2) |>.or fallback then send vs e
      | .unknown => do
          for (_, e) in cases do send vs e
          if let some e := fallback then send vs e

private def walk {f : List Machine.Signature} {l : List Nat} {r n : Nat} (vs : Values n) :
    Body f l r n → StateM (Info l) Unit
  | .done exit => propagate vs exit
  | .step op next => walk (outputs vs op ++ vs) next

private def analyze {f : List Machine.Signature} {s : Machine.Signature} (d : Def f s) : Info d.layout := Id.run do
  let mut info : Info d.layout := ({} : Info d.layout).insert d.entry.index
    (Vector.replicate _ .unknown)
  let mut changed := true
  while changed do
    let old := info
    for b in List.finRange d.layout.length do
      if let some vs := info.get? b then info := (walk vs (d.blocks.get b)).run info |>.2
    changed := !info.beq old
  return info

private def rewrite {f : List Machine.Signature} {l : List Nat} {r n m : Nat}
    (vs : Values n) (σ : Subst n m) : Body f l r n → Body f l r m
  | .done exit => .done (Id.run (exit.traverse (fun i => (replace vs (.var i)).subst σ) pure))
  | .step (m := k) op next =>
      let values := outputs vs op ++ vs
      let op := op.map (fun a => (replace vs a).subst σ)
      match Scalar.fold op with
      | some xs => rewrite values (xs ++ Vector.ofFn σ).get next
      | none => .step op (rewrite values (σ.lift k) next)

/-- Propagate scalar constants through executable CFG edges before demand and allocation.
Operations retain their execution order; later dead-code elimination removes unused total
results. Division's success word is known for a constant divisor, including zero. -/
public def run {s : Oria.Program.ClosedProgram} (p : Machine.Program s) :
    Except Diagnostic (Machine.Program s) := do
  let definitions ← Data.IndexedVector.ofFnM fun i => do
    let d := p.definitionAt i
    let info := analyze d
    let blocks := Data.IndexedVector.ofFn fun b =>
      rewrite (info.getD b (Vector.replicate _ .unknown)) Atom.var (d.blocks.get b)
    Machine.controlFlow s.members[memberPosition p.table s i].source {d with blocks}
  return {p with definitions}

end Oria.Optimize.Constants
