module

import Oria
import Oria.Proofs.BackendUtil
meta import Oria
meta import Oria.Proofs.BackendUtil

namespace Oria.Proofs.Operators

open Oria Lean Lean.Elab.Command

example (x : Val Int32) : Val Bool := x < 0
example (x : Val Int32) : Val Bool := 0 <= x
example (x : Val Int32 .persistent) : Val Bool := x > 0 && x <= 10
example (x y : Val Int32) : Val Bool := x >= y || x == y
example (x y : Val Int32) : Val Bool := x != y
example (b : Val Bool) : Val Bool := !b || b && true
example (a b : Val Bool) : Val Bool := a == b
example : Val Bool := true == false
example (x : Val Int32) (n : Nat) : Val Bool := x < n
example (x : Val Int32) (n : Int32) : Val Bool := x == n
example (x : Nat) : Prop := x <= 10
example (x : Int) : Bool := x < 0 || x > 10
#guard 1 < 2
#guard !(true && false)
#guard (some 1 == some 1)

@[mcfunction]
private def between (x : Val Int32) : Prog .pure Bool := Prog.pure (0 < x && x < 10)

@[mcfunction]
private def widened : Prog ⟨Req.none, Eff.world⟩ Int32 :=
  (Prog.pure (7 : Val Int32)).weaken

example [Object A a] (p : Prog g A r) (h : g.Below k) : Prog k A r := p.weaken h
example : ¬Grade.Below ⟨Req.none, Eff.world⟩ .pure := by decide

run_cmd do
  let ⟨source, machine⟩ ← BackendUtil.compile #[⟨_, between.ref⟩, ⟨_, widened.ref⟩]
  let some pos := source.position? ``between | throwError "missing short-circuit example"
  let fn := machine.definitionAt (IR.Machine.referenceAt machine.table source pos).index
  unless fn.layout.length > 1 do throwError "Boolean conjunction lost its branches"
  let some pos := source.position? ``widened | throwError "missing grade example"
  let fn := machine.definitionAt (IR.Machine.referenceAt machine.table source pos).index
  match fn.block fn.entry with
  | .done (.ret values) =>
      unless values.toList == [.lit 7] do throwError "grade weakening changed the result"
  | _ => throwError "grade weakening introduced instructions"

end Oria.Proofs.Operators
