module

public import Oria.IR.Machine.Program
public import Oria.IR.Machine.Transform
public import Std.Data.DHashMap.Basic

namespace Oria.Analysis.Bits

open Oria.IR Oria.IR.Machine

/-- A set bit guarantees a word belongs to `{0, 1}`. Missing rows start optimistic. -/
public structure FunctionInfo (layout : List Nat) (r : Nat) where
  result : BitVec r := BitVec.allOnes r
  blocks : Std.DHashMap (Fin layout.length) (fun i => BitVec (layout.get i)) := {}

public instance {l : List Nat} {r : Nat} : Inhabited (FunctionInfo l r) := ⟨{}⟩
public instance {l : List Nat} {r : Nat} : BEq (FunctionInfo l r) where
  beq a b := a.result == b.result && a.blocks.beq b.blocks

public abbrev Info {s : Oria.Program.ClosedProgram} (p : IR.Machine.Program s) :=
  Std.DHashMap (Fin (signatures p.table s).length) fun i =>
    FunctionInfo (p.definitionAt i).layout ((signatures p.table s).get i).result

public def functionInfo {s : Oria.Program.ClosedProgram} (p : IR.Machine.Program s)
    (info : Info p) (i : Fin (signatures p.table s).length) := info.getD i {}

public def parameters {s : Oria.Program.ClosedProgram} (p : IR.Machine.Program s)
    (info : Info p) (i : Fin (signatures p.table s).length) (b : Fin (p.definitionAt i).layout.length) :=
  (functionInfo p info i).blocks.getD b (BitVec.allOnes _)

@[expose] public def atom {n : Nat} (bits : BitVec n) : Atom n → Bool
  | .var i => bits.getLsb i
  | .lit v => v == 0 || v == 1

/-- Interpretation of a guaranteed bit, independent of its source-language type. -/
public def IsBit (v : Int32) : Prop := v = 0 ∨ v = 1

public theorem atom_sound {n : Nat} (bits : BitVec n) (value : Fin n → Int32)
    (known : ∀ i, bits.getLsb i → IsBit (value i)) (v : Atom n) (h : atom bits v) :
    IsBit (match v with | .var i => value i | .lit v => v) := by
  cases v with
  | var i => exact known i h
  | lit v => simpa [atom, IsBit] using h

private def arguments {n m : Nat} (bits : BitVec n) (vs : Vector (Atom n) m) : BitVec m :=
  (List.finRange m).foldl (init := 0) fun out i =>
    if atom bits (vs.get i) then out ||| BitVec.ofNat m (1 <<< i.val) else out

/-- Intrinsic scalar guarantees and the current normal-return summaries of calls. -/
public def outputs {s : Oria.Program.ClosedProgram} {n m : Nat}
    (p : IR.Machine.Program s) (info : Info p) : Op (signatures p.table s) n m → BitVec m
  | .unary .not _ => 1
  | .binary .le _ _ | .binary .lt _ _ | .binary .eq _ _ | .binary .beq _ _ => 1
  | .command _ | .division _ _ => 1
  | .call ref _ => ref.typeCorrect ▸ (functionInfo p info ref.index).result
  | _ => 0

public def extend {n m : Nat} (bits : BitVec n) (fresh : BitVec m) : BitVec (m + n) :=
  (bits.setWidth (m + n) <<< m) ||| fresh.setWidth (m + n)

private def walk {s : Oria.Program.ClosedProgram} {n : Nat}
    (p : IR.Machine.Program s) (i : Fin (signatures p.table s).length) (bits : BitVec n) :
    Body (signatures p.table s) (p.definitionAt i).layout ((signatures p.table s).get i).result n →
      StateM (Info p) Unit
  | .step op next => do
      walk p i (extend bits (outputs p (← get) op)) next
  | .done exit => do
      let _ ← exit.traverse Atom.var fun e => do
        let info ← get
        let fn := functionInfo p info i
        let incoming := e.target.typeCorrect.symm ▸ arguments bits e.values
        let row := parameters p info i e.target.index &&& incoming
        set (info.insert i { fn with blocks := fn.blocks.insert e.target.index row })
        pure e
      if let .ret vs := exit then
        modify fun info =>
          let fn := functionInfo p info i
          info.insert i { fn with result := fn.result &&& arguments bits vs }

/-- Descending finite bit masks; every function entry accepts arbitrary scalar arguments. -/
public def analyze {s : Oria.Program.ClosedProgram} (p : IR.Machine.Program s) : Info p := Id.run do
  let mut info : Info p := {}
  for i in List.finRange (signatures p.table s).length do
    info := info.insert i { blocks := ({} : Std.DHashMap _ _).insert (p.definitionAt i).entry.index 0 }
  let mut changed := true
  while changed do
    let old := info
    for i in List.finRange (signatures p.table s).length do
      for b in List.finRange (p.definitionAt i).layout.length do
        info := (walk p i (parameters p info i b) ((p.definitionAt i).blocks.get b)).run info |>.2
    changed := !info.beq old
  return info

end Oria.Analysis.Bits
