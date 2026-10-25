module

public import Oria.IR.Common.Signature

namespace Oria.IR

public inductive DefKey where
  | named (decl : Lean.Name)
  deriving BEq, DecidableEq, Hashable, Repr

public structure DeclRef (sig : Signature) where
  key : DefKey
  deriving Repr

namespace DeclRef

public def named {sig : Signature} (decl : Lean.Name) : DeclRef sig :=
  ⟨.named decl⟩

/-- A declaration reference carrying its source signature. -/
public structure Some where
  sig : Signature
  ref : DeclRef sig

end DeclRef

/--
An unresolved nominal constructor reference. Its indices state the claimed telescope; a later
catalogue pass must resolve the name and issue constructor-closure evidence. Physical tags are
chosen still later by representation planning.
-/
public structure CtorRef (owner : TypeId) (fields : List ObjTy) where
  name : Lean.Name
  deriving BEq, DecidableEq, Repr

/-- Logical constructor and its exact payload telescope, shared by Tree and Cont. -/
public inductive Constructor : ObjTy → List ObjTy → Type where
  | data {owner : TypeId} {fields : List ObjTy} : CtorRef owner fields → Constructor (.data owner) fields
  | none {a : ObjTy} : Constructor (.option a) []
  | some {a : ObjTy} : Constructor (.option a) [a]

namespace Constructor

public def name {a : ObjTy} {fields : List ObjTy} : Constructor a fields → Lean.Name
  | .data reference => reference.name
  | .none => ``Option.none
  | .some => ``Option.some

end Constructor

end Oria.IR
