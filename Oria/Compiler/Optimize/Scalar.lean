module

public import Oria.IR.Machine.Transform

namespace Oria.Optimize.Scalar

open Oria.IR Oria.IR.Machine

public def word (b : Bool) : Int32 := if b then 1 else 0

public def binary {a b c : ObjTy} : BinaryOp a b c → Int32 → Int32 → Int32
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .le, a, b => word (Condition.test .le a b)
  | .lt, a, b => word (Condition.test .lt a b)
  | .eq, a, b => word (Condition.test .eq a b)
  | .beq, a, b => word (Condition.test .beq a b)

/-- Total scalar identities over wrapping I32 words. Division by one substitutes
its explicit success component; an unknown divisor retains native failure.
The same rules serve CFG propagation and edge-local jump threading. -/
public def fold {f : List Machine.Signature} {n m : Nat} : Op f n m → Option (Vector (Atom n) m)
  | .unary .neg (.lit v) => some #v[.lit (-v)]
  | .unary .not (.lit v) => some #v[.lit (word (v == 0))]
  | .binary op (.lit l) (.lit r) => some #v[.lit (binary op l r)]
  | .binary .add v (.lit 0) | .binary .add (.lit 0) v
  | .binary .sub v (.lit 0)
  | .binary .mul v (.lit 1) | .binary .mul (.lit 1) v => some #v[v]
  | .binary .mul _ (.lit 0) | .binary .mul (.lit 0) _ => some #v[.lit 0]
  | .binary .sub l r => if l == r then some #v[.lit 0] else none
  | .binary .eq l r | .binary .beq l r | .binary .le l r =>
      if l == r then some #v[.lit 1] else none
  | .binary .lt l r => if l == r then some #v[.lit 0] else none
  | .division v (.lit 1) => some #v[.lit 1, v]
  | .division (.lit l) (.lit r) => (Oria.I32.divide l r).map fun v => #v[.lit 1, .lit v]
  | _ => none

end Oria.Optimize.Scalar
