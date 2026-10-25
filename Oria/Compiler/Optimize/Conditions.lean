module

public import Oria.Compiler.Analysis.Bits
import Oria.Compiler.Analysis.Liveness
import Oria.Compiler.Optimize.ControlFlow
import Std.Data.DHashMap.Basic

namespace Oria.Optimize.Conditions

open Oria.IR Oria.IR.Machine

private abbrev Predicate (n : Nat) := Bool × Condition (Atom n)
private abbrev Preds (n : Nat) := Vector (Option (Predicate n)) n

private instance {n : Nat} : BEq (Condition (Atom n)) where
  beq
    | .isTrue a, .isTrue b => a == b
    | .compare .le a b, .compare .le c d
    | .compare .lt a b, .compare .lt c d
    | .compare .eq a b, .compare .eq c d
    | .compare .beq a b, .compare .beq c d => a == c && b == d
    | _, _ => false

private theorem flipped (positive value : Bool) :
    (if !positive then value else !value) = !(if positive then value else !value) := by
  cases positive <;> cases value <;> rfl

private def predicate {f : List IR.Machine.Signature} {n m : Nat} (preds : Preds n) :
    Op f n m → Vector (Option (Predicate n)) m
  | .unary .not v =>
      let previous := match v with | .var i => preds[i] | _ => none
      #v[some ((previous.map fun p => (!p.1, p.2)).getD (true, .compare .eq v (.lit 0)))]
  | .binary .le l r => #v[some (true, .compare .le l r)]
  | .binary .lt l r => #v[some (true, .compare .lt l r)]
  | .binary .eq l r => #v[some (true, .compare .eq l r)]
  | .binary .beq l r => #v[some (true, .compare .beq l r)]
  | _ => Vector.replicate _ none

private def fuse {n : Nat} (preds : Preds n) :
    Condition (Atom n) → Predicate n
  | .isTrue (.var i) =>
      (preds.get i).getD (true, .isTrue (.var i))
  | c => (true, c)

private def branch {l : List Nat} {r n : Nat} (preds : Preds n)
    (c : Condition (Atom n)) (yes no : Edge l n) : Terminator l r n :=
  let (positive, c) := fuse preds c
  if positive then .branch c yes no else .branch c no yes

private def bitReturn {f : List IR.Machine.Signature} {s : IR.Machine.Signature} {n : Nat}
    (d : Def f s) (result : BitVec s.result) (v : Atom n) (yes no : Edge d.layout n) :
    Option (Vector (Atom n) s.result) := do
  let .done (.ret xs) := d.block yes.target | none
  let .done (.ret ys) := d.block no.target | none
  Vector.ofFnM fun i => do
    if !result.getLsb i then return .lit 0
    let x := xs[i].subst yes.values.get
    let y := ys[i].subst no.values.get
    if x == y then some x else if x == .lit 1 && y == .lit 0 then some v else none

private def simplify {f : List IR.Machine.Signature} {s : IR.Machine.Signature} {n : Nat}
    (d : Def f s) (result : BitVec s.result) (bits : BitVec n)
    (preds : Preds n) :
    Terminator d.layout s.result n → Terminator d.layout s.result n
  | .branch c yes no =>
      match c with
      | .isTrue v =>
          match if Analysis.Bits.atom bits v then bitReturn d result v yes no else none with
          | some values => .ret values
          | none => branch preds c yes no
      | _ => branch preds c yes no
  | .switch v cases fallback =>
      match Analysis.Bits.atom bits v,
          cases.find? (fun c => c.1 == 0), cases.find? (fun c => c.1 == 1) with
      | true, some (_, no), some (_, yes) => branch preds (.isTrue v) yes no
      | _, _, _ => .switch v cases fallback
  | exit => exit

private def extend {f : List IR.Machine.Signature} {n m : Nat} (preds : Preds n) (op : Op f n m) :
    Preds (m + n) :=
  let shift := Option.map (fun p : Predicate n => (p.1, p.2.map (fun v => v.weaken m)))
  (predicate preds op).map shift ++ preds.map shift

private abbrev Info (l : List Nat) := Std.DHashMap (Fin l.length) (fun i => Preds (l.get i))

-- A recipe crosses an edge only through operands already supplied by that edge.
-- Words are immutable SSA snapshots, so intervening effects preserve these relations.
private def send {l : List Nat} {n : Nat} (preds : Preds n) (e : Edge l n) : StateM (Info l) Unit := do
  let transport : Atom n → Option (Atom e.arity)
    | .lit v => some (.lit v)
    | a@(.var _) => Atom.var <$> (List.finRange e.arity).find? (fun j => e.values[j] == a)
  let incoming := e.target.typeCorrect.symm ▸ e.values.map fun
    | .lit _ => none
    | .var i => preds[i].bind fun p => (p.1, ·) <$> p.2.traverse transport
  modify fun info => info.insert e.target.index <|
    match info.get? e.target.index with
    | none => incoming
    | some old => old.zipWith (fun a b => if a == b then a else none) incoming

private def propagate {f : List IR.Machine.Signature} {l : List Nat} {r n : Nat}
    (preds : Preds n) : Body f l r n → StateM (Info l) Unit
  | .step op next => propagate (extend preds op) next
  | .done exit => do
      discard <| exit.traverse Atom.var (fun e => do send preds e; pure e)

private def analyze {f : List IR.Machine.Signature} {s : IR.Machine.Signature} (d : Def f s) : Info d.layout := Id.run do
  let mut info : Info d.layout := ({} : Info d.layout).insert d.entry.index (Vector.replicate _ none)
  let mut changed := true
  while changed do
    let old := info
    for b in List.finRange d.layout.length do
      if let some preds := info.get? b then
        info := (propagate preds (d.blocks.get b)).run info |>.2
    changed := !info.beq old
  return info

private def body {s : Oria.Program.ClosedProgram} {sig : IR.Machine.Signature} {n : Nat}
    (p : IR.Machine.Program s) (info : Analysis.Bits.Info p)
    (d : Def (signatures p.table s) sig) (result : BitVec sig.result)
    (bits : BitVec n) (preds : Preds n) :
    Body (signatures p.table s) d.layout sig.result n → Body (signatures p.table s) d.layout sig.result n
  | .done exit => .done (simplify d result bits preds exit)
  | .step op next =>
      .step op (body p info d result (Analysis.Bits.extend bits (Analysis.Bits.outputs p info op)) (extend preds op) next)

/-- Carry agreed predicate recipes through CFG edges and lower exhaustive bit switches.
Scalar observations retain their producer; demand pruning removes branch-only results. -/
public def run {s : Oria.Program.ClosedProgram} (p : IR.Machine.Program s) :
    Except Diagnostic (IR.Machine.Program s) := do
  let bits := Analysis.Bits.analyze p
  let demand := Analysis.Demand.analyze p
  let definitions ← Data.IndexedVector.ofFnM fun i => do
    let d := p.definitionAt i
    let facts := analyze d
    let blocks := Data.IndexedVector.ofFn fun b =>
      body p bits d (Analysis.Demand.functionInfo p demand i).result
        (Analysis.Bits.parameters p bits i b)
        (facts.getD b (Vector.replicate _ none)) (d.blocks.get b)
    Optimize.Machine.controlFlow s.members[memberPosition p.table s i].source { d with blocks }
  return { p with definitions }

end Oria.Optimize.Conditions
