module

public import Oria.IR.Common.Schema
public import Oria.IR.Common.Reference

namespace Oria.Representation

open Oria Oria.IR

/-- A pointer word retains its logical pointee type for later memory passes. -/
public inductive WordKind where
  | scalar
  | pointer (type : ObjTy)
  deriving BEq, DecidableEq, Repr

/-- Immutable heap payload. The constructor tag occupies a separate header. -/
public structure HeapLayout (slots : Nat) where
  type : ObjTy
  constructor : Lean.Name
  tag : Int32
  payload : Vector WordKind slots
  deriving Repr

/-- The scalar-word contents of one named persistent root. -/
public structure RootLayout (slots : Nat) where
  name : Lean.Name
  words : Vector WordKind slots
  deriving Repr

namespace HeapLayout

/-- A sentinel bit retains the slot count, followed by one bit per pointer slot. -/
public def scanCode {n : Nat} (layout : HeapLayout n) : Nat :=
  layout.payload.toList.foldr (fun kind code =>
    2 * code + match kind with | .scalar => 0 | .pointer _ => 1) 1

end HeapLayout

end Oria.Representation
