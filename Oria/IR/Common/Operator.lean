module

public import Oria.IR.Common.I32
public import Oria.IR.Common.Type

namespace Oria.IR

/-- Strict typed unary operators shared by structured expressions and continuation IR. -/
public inductive UnaryOp : ObjTy → ObjTy → Type where
  | neg : UnaryOp .i32 .i32
  | not : UnaryOp .bool .bool

/--
Strict typed binary operators shared by structured expressions and continuation IR. Both operands
are evaluated before the operator; short-circuiting operations therefore do not belong here.
-/
public inductive BinaryOp : ObjTy → ObjTy → ObjTy → Type where
  | add : BinaryOp .i32 .i32 .i32
  | sub : BinaryOp .i32 .i32 .i32
  | mul : BinaryOp .i32 .i32 .i32
  | le : BinaryOp .i32 .i32 .bool
  | lt : BinaryOp .i32 .i32 .bool
  | eq : BinaryOp .i32 .i32 .bool
  | beq : BinaryOp .bool .bool .bool

end Oria.IR
