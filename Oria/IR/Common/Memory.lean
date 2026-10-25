module

public import Oria.IR.Common.Reference
public import Oria.IR.Common.Nbt
public import Oria.Effect.Labels

namespace Oria.Persistent

@[expose] public def readGrade : Grade := ⟨Req.none, Eff.persistentRead⟩
@[expose] public def writeGrade : Grade := ⟨Req.none, Eff.persistentWrite⟩
@[expose] public def allocGrade : Grade := ⟨Req.none, Eff.persistentAlloc⟩
@[expose] public def stateGrade : Grade := (readGrade.seq allocGrade).seq writeGrade

end Oria.Persistent

namespace Oria.IR

/-- A source root identity with the logical type of its current value. -/
public structure RootRef (a : ObjTy) where
  name : Lean.Name
  deriving BEq, DecidableEq, Repr

namespace RootRef

public structure Some where
  type : ObjTy
  ref : RootRef type

end RootRef

/-- Arena and persistent memory operations, with their complete operand telescope and exact grade. -/
public inductive MemoryOp : Grade → List ObjTy → ObjTy → Type where
  | nbt {as : List ObjTy} {a : ObjTy} : (op : Nbt.Op as a) → MemoryOp op.grade as a
  | persist {a : ObjTy} : MemoryOp Persistent.allocGrade [a] a
  | rootGet {a : ObjTy} : RootRef a → MemoryOp Persistent.readGrade [] a
  | rootSet {a : ObjTy} : RootRef a → MemoryOp Persistent.writeGrade [a] .unit
  | refNew {a : ObjTy} : MemoryOp Persistent.allocGrade [a] (.ref a)
  | refGet {a : ObjTy} : MemoryOp Persistent.readGrade [.ref a] a
  | refSet {a : ObjTy} : MemoryOp Persistent.writeGrade [.ref a, a] .unit

namespace MemoryOp

public def root? {g : Grade} {as : List ObjTy} {a : ObjTy} : MemoryOp g as a → Option RootRef.Some
  | .rootGet ref | .rootSet ref => some ⟨_, ref⟩
  | _ => none

end MemoryOp

end Oria.IR
