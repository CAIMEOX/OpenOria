module

public import Oria.IR.Machine.Transform
import Oria.Compiler.Optimize.Scalar
import Std.Data.HashSet.Basic

namespace Oria.Optimize.Machine

open Oria.IR Oria.IR.Machine

variable {f : List IR.Machine.Signature} {s : IR.Machine.Signature} {l : List Nat} {r n : Nat}

private def sameEdge (a b : Edge l n) : Bool :=
  if h : a.arity = b.arity then
    a.target.index == b.target.index && (h ▸ a.values) == b.values
  else false

private def foldExit : Terminator l r n → Terminator l r n
  | .branch c yes no =>
      match c.traverse (fun | .lit v => some v | .var _ => none) with
      | some c => .jump (if c.eval id then yes else no)
      | none => if sameEdge yes no then .jump yes else .branch c yes no
  | .switch (.lit v) cases fallback =>
      match (cases.find? (fun (tag, _) => tag == v)).map (·.2) |>.or fallback with
      | some e => .jump e
      | none => .switch (.lit v) [] none
  | exit => exit

private def reducedExit {n m : Nat} (σ : Subst n m) :
    Body f l r n → Option (Terminator l r m)
  | .done exit => some (Id.run (exit.traverse σ pure))
  | .step op next => do
      let xs ← Scalar.fold (op.map (Atom.subst σ))
      reducedExit (xs ++ Vector.ofFn σ).get next

/-- Follow a finite block path through fully reducible scalar prefixes. -/
private def forward (d : Def f s) : Nat → {n : Nat} → Edge d.layout n → Edge d.layout n
  | 0, _, e => e
  | fuel + 1, _, e =>
      match reducedExit e.values.get (d.block e.target) with
      | some exit =>
          match foldExit exit with
          | .jump next =>
              if next.target.index == e.target.index then e else forward d fuel next
          | _ => e
      | none => e

private def thread (d : Def f s) : Def f s :=
  { d with blocks := Data.IndexedVector.ofFn fun i =>
      Id.run ((d.blocks.get i).rewrite Atom.var fun exit => do
        let exit ← exit.traverse Atom.var (fun e => pure (forward d d.layout.length e))
        if let .branch _ yes no := exit then
          if let .done (.ret xs) := d.block yes.target then
            if let .done (.ret ys) := d.block no.target then
              let xs := xs.map (Atom.subst yes.values.get)
              let ys := ys.map (Atom.subst no.values.get)
              if xs == ys then return .done (.ret xs)
        return .done (foldExit exit)) }

private def successors (body : Body f l r n) : List (Fin l.length) :=
  let ⟨_, exit⟩ := body.exit
  (exit.traverse Atom.var (fun e => do
    modify (e.target.index :: ·)
    pure e) : StateM (List (Fin l.length)) _).run [] |>.2

private def reachable (d : Def f s) : Std.HashSet Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut pending := [d.entry.index]
  while let i :: rest := pending do
    pending := rest
    unless seen.contains i.val do
      seen := seen.insert i.val
      pending := successors (d.blocks.get i) ++ pending
  return seen

/-- Compact the reachable telescope; every reconstructed edge carries its target arity. -/
private def compact (source : Lean.Name) (d : Def f s) : Except Diagnostic (Def f s) := do
  let live := reachable d
  let kept := (List.finRange d.layout.length).filter (fun i => live.contains i.val)
  let layout := kept.map d.layout.get
  let ref {a : Nat} (old : Scope.Var Unit d.layout a) :
      Except Diagnostic (Scope.Var Unit layout a) := do
    let some i := kept.findFinIdx? (· == old.index)
      | throw (.unsupportedMachineLowering source)
    let j : Fin layout.length := ⟨i.val, by simp [layout]⟩
    if h : layout.get j = a then pure (h ▸ Scope.Var.ofIndex Unit j)
    else throw (.unsupportedMachineLowering source)
  let entry ← ref d.entry
  let blocks ← Data.IndexedVector.ofFnM fun i : Fin layout.length => do
    let old := kept.get ⟨i.val, by simpa [layout] using i.isLt⟩
    let body ← (d.blocks.get old).rewrite Atom.var fun exit =>
      Body.done <$> exit.traverse Atom.var (fun e => do return ⟨← ref e.target, e.values⟩)
    have arity : d.layout.get old = layout.get i := by simp [layout, old]
    pure (arity ▸ body)
  return ⟨layout, entry, blocks⟩

private def incoming (d : Def f s) : Array Nat :=
  (List.finRange d.layout.length).foldl (init := Array.replicate d.layout.length 0) fun counts i =>
    (successors (d.blocks.get i)).foldl (fun counts j => counts.modify j.val (· + 1)) counts

/-- Only an unconditional, uniquely owned successor is spliced into the current prefix. -/
private def merge (d : Def f s) (uses : Array Nat) :
    Nat → {n : Nat} → Body f d.layout s.result n → Body f d.layout s.result n
  | 0, _, body => body
  | fuel + 1, _, body => Id.run (body.rewrite Atom.var fun exit => do
      let exit := foldExit exit
      if let .jump e := exit then
        if e.target.index != d.entry.index && uses[e.target.index.val]? == some 1 then
          return merge d uses fuel ((d.block e.target).subst e.values.get)
      return .done exit)

/-- Shrink CFGs before demand and register allocation, retaining function signatures and loops. -/
public def controlFlow (source : Lean.Name) (d : Def f s) : Except Diagnostic (Def f s) := do
  let live ← compact source (thread d)
  let uses := incoming live
  let merged := { live with blocks := Data.IndexedVector.ofFn (fun i =>
      merge live uses live.layout.length (live.blocks.get i)) }
  let result ← compact source merged
  if _h : result.layout.length < d.layout.length then controlFlow source result else pure result
termination_by d.layout.length

end Oria.Optimize.Machine
