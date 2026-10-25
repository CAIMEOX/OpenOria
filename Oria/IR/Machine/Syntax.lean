module

public import Oria.IR.Common.Operator
public import Oria.IR.Machine.Condition
public import Oria.IR.Common.Scope
public import Oria.Command.Execute
public import Init.Data.Vector.OfFn
public import Oria.IR.Representation.Syntax
public import Oria.IR.Common.Nbt

namespace Oria.IR.Machine

/-- Full scalar-word calling convention before demand pruning. -/
public structure Signature where
  args : Nat
  result : Nat
  deriving BEq, DecidableEq, Repr

/-- A scalar literal or a variable in the current instruction prefix. -/
public inductive Atom (n : Nat) where
  | var : Fin n → Atom n
  | lit : Int32 → Atom n
  deriving BEq, DecidableEq, Repr

namespace Atom

public def weaken {n : Nat} (a : Atom n) (m : Nat) : Atom (m + n) :=
  match a with
  | .var i => .var ⟨m + i.val, by omega⟩
  | .lit value => .lit value

end Atom

/-- Every edge carries exactly its target's declared parameter count. -/
public structure Edge (layout : List Nat) (n : Nat) where
  {arity : Nat}
  target : Scope.Var Unit layout arity
  values : Vector (Atom n) arity

/-- Commands and calls produce ordinary scalar result tuples. -/
public inductive Op (functions : List Signature) (n : Nat) : Nat → Type where
  /-- Native success followed by a quotient, whose value is used only on success. -/
  | division : Atom n → Atom n → Op functions n 2
  | checkpoint : (forced : Bool) → Op functions n 0
  | nbt {as : List ObjTy} {a : ObjTy} : (operation : Nbt.Op as a) → Args (fun _ => Atom n) as →
      Op functions n operation.width
  | unary {a b : ObjTy} : UnaryOp a b → Atom n → Op functions n 1
  | binary {a b c : ObjTy} : BinaryOp a b c → Atom n → Atom n → Op functions n 1
  | allocate {slots : Nat} : Representation.HeapLayout slots → Vector (Atom n) slots → Op functions n 1
  | tag : Atom n → Op functions n 1
  | project {slots : Nat} : Representation.HeapLayout slots → Atom n → Op functions n slots
  | promote : ObjTy → Atom n → Op functions n 1
  | rootGet {slots : Nat} : Representation.RootLayout slots → Op functions n slots
  | rootSet {slots : Nat} : Representation.RootLayout slots → Vector (Atom n) slots → Op functions n 0
  | refNew {slots : Nat} : Representation.HeapLayout slots → Vector (Atom n) slots → Op functions n 1
  | refGet {slots : Nat} : Representation.HeapLayout slots → Atom n → Op functions n slots
  | refSet {slots : Nat} : Representation.HeapLayout slots → Atom n → Vector (Atom n) slots →
      Op functions n 0
  | command {route : Oria.Command.Signature} : Command.Call (fun _ => Atom n) route → Op functions n 2
  | call {sig : Signature} : Scope.Var Unit functions sig → Vector (Atom n) sig.args →
      Op functions n sig.result
  | execute {params : Nat} : Execute.Scope (fun _ => Atom n) → (canFail : Bool) →
      Scope.Var Unit functions ⟨params, canFail.toNat + 1⟩ → Vector (Atom n) params → Op functions n 0

public inductive Terminator (layout : List Nat) (result n : Nat) where
  | ret : Vector (Atom n) result → Terminator layout result n
  | jump : Edge layout n → Terminator layout result n
  | branch : Condition (Atom n) → Edge layout n → Edge layout n → Terminator layout result n
  | switch : Atom n → List (Int32 × Edge layout n) → Option (Edge layout n) →
      Terminator layout result n

/-- New results precede the existing instruction-prefix context. -/
public inductive Body (functions : List Signature) (layout : List Nat) (result : Nat) :
    Nat → Type where
  | done {n : Nat} : Terminator layout result n → Body functions layout result n
  | step {n m : Nat} : Op functions n m → Body functions layout result (m + n) →
      Body functions layout result n

end Oria.IR.Machine
