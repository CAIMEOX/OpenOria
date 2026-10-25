module

public import Oria.IR.Machine.Definition
public import Oria.IR.Program.Closed
public import Oria.IR.Representation.Syntax
public import Oria.IR.Representation.Persistent

namespace Oria.IR.Machine

/-- Flattening is the same at parameters, joins, and function results. -/
@[expose] public def signature (table : Representation.Table) (sig : Oria.Signature) : Signature :=
  ⟨table.arity sig.args, if sig.grade.canFail then 1 + table.width sig.result else table.width sig.result⟩

@[expose] public def signatures (table : Representation.Table) (source : Oria.Program.ClosedProgram) : List Signature :=
  List.ofFn fun i : Fin source.members.size =>
    signature table source.members[i].signature

public def referenceAt (table : Representation.Table) (source : Oria.Program.ClosedProgram)
    (i : Fin source.members.size) :
    Scope.Var Unit (signatures table source) (signature table source.members[i].signature) := by
  have index : i.val < (signatures table source).length := by simp [signatures]
  let ref := Scope.Var.ofIndex Unit (Γ := signatures table source) ⟨i.val, index⟩
  have shape : (signatures table source).get ⟨i.val, index⟩ =
      signature table source.members[i].signature := by simp [signatures]
  exact shape ▸ ref

@[expose] public def memberPosition (table : Representation.Table) (source : Oria.Program.ClosedProgram)
    (i : Fin (signatures table source).length) : Fin source.members.size :=
  ⟨i.val, by simpa [signatures] using i.isLt⟩

/-- Each source member owns one physical CFG; source roots identify observable results. -/
public structure Program (source : Oria.Program.ClosedProgram) where
  table : Representation.Table
  definitions : Data.IndexedVector fun i : Fin (signatures table source).length =>
    Def (signatures table source) ((signatures table source).get i)
  persistent : Representation.Persistent.PlanTable := ⟨0, #v[], #[]⟩

namespace Program

public def definitionAt {source : Oria.Program.ClosedProgram}
    (program : Program source) (i : Fin (signatures program.table source).length) :
    Def (signatures program.table source) ((signatures program.table source).get i) :=
  program.definitions.get i

end Program
end Oria.IR.Machine
