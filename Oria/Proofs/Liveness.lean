module

import Oria.Compiler.Analysis.Machine
import Oria.Compiler.Analysis.Liveness
meta import Oria.Compiler.Analysis.Liveness

namespace Oria.Proofs.Liveness

open Oria Oria.IR

example {n m : Nat} (values : Vector (Machine.Atom n) m) :
    Analysis.Machine.uses values 0 = 0 := Analysis.Machine.uses_zero values

example {n : Nat} (i : Fin n) (m : Nat) :
    Analysis.Machine.number (⟨m + i.val, by omega⟩ : Fin (m + n)) =
      Analysis.Machine.number i := by simp

example {functions : List Machine.Signature} {n : Nat}
    (l r : Machine.Atom n)
    (params : {sig : Machine.Signature} → Scope.Var Unit functions sig → BitVec sig.args) :
    Analysis.Machine.inputs params (.binary .add l r) 0 = 0 := by rfl

example {functions : List Machine.Signature} {n slots : Nat}
    (values : Vector (Machine.Atom n) slots)
    (root : Representation.RootLayout slots)
    (params : {sig : Machine.Signature} → Scope.Var Unit functions sig → BitVec sig.args) :
    Analysis.Machine.inputs params (.rootSet root values) 0 =
      Analysis.Machine.uses values (BitVec.allOnes slots) := by rfl

private def sample : Machine.Body [⟨1, 1⟩] [] 1 2 :=
  .step (.binary .add (.var 0) (.var 1)) <|
    .step (.call (sig := ⟨1, 1⟩) Scope.Var.head #v[.var 0]) <|
      .step (.binary .add (.var 2) (.var 0)) <|
        .done (.ret #v[.var 0])

private def facts : Analysis.Liveness.Block 2 := Analysis.Liveness.scan
  (fun _ => BitVec.allOnes _)
  (Analysis.Machine.exit (layout := []) (fun ref => Fin.elim0 ref.index) 1)
  (sample : Machine.Body [⟨1, 1⟩] [] 1 2)

#guard facts.parameters == 3
#guard facts.points.map (·.across.toNat) == #[1, 2, 0]
#guard facts.points.map (·.callee) == #[none, some 0, none]
#guard facts.points[1]?.any (·.acrossValue 1)
#guard !facts.points[1]?.any (·.acrossValue 2)
#guard facts.ranges == #[some ⟨0, 2⟩, some ⟨0, 6⟩, some ⟨2, 4⟩,
  some ⟨4, 6⟩, some ⟨6, 8⟩]

end Oria.Proofs.Liveness
