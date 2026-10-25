module

import Oria
import Oria.IR.Cont.Semantics
meta import Oria

namespace Oria.Proofs.Failure

open Oria Oria.IR Oria.IR.Cont Oria.Semantics.Cont

/-- A failure exit preserves the current state. -/
theorem failure_state {s : Type} {Γ : List ObjTy} {a : ObjTy}
    {j : List (List ObjTy)} (model : Model s) (fuel : Nat)
    (env : Env Γ) (joins : JoinEnv a j s) (state : s) :
    (eval model (fuel + 1) env joins .fail).run state = (some .failed, state) := rfl

/-- Recovery receives the state after the failing operation, including preceding effects. -/
theorem invoke_failure {s : Type} {Γ : List ObjTy} {a b : ObjTy}
    {g : Grade} {j : List (List ObjTy)} (model : Model s) (fuel : Nat)
    (env : Env Γ) (joins : JoinEnv b j s) (op : Op Γ g a)
    (next : Comp (a :: Γ) b j) (handler : Comp Γ b j) (before after : s)
    (h : (evalOp model env op).run before = (.failed, after)) :
    (eval model (fuel + 1) env joins (.invoke op next handler)).run before =
      (eval model fuel env joins handler).run after := by
  simp [eval, h]
  rfl

/-- Only normal completion extends the continuation's value context. -/
theorem invoke_normal {s : Type} {Γ : List ObjTy} {a b : ObjTy}
    {g : Grade} {j : List (List ObjTy)} (model : Model s) (fuel : Nat)
    (env : Env Γ) (joins : JoinEnv b j s) (op : Op Γ g a)
    (next : Comp (a :: Γ) b j) (handler : Comp Γ b j) (before after : s)
    (value : Value a) (h : (evalOp model env op).run before = (.returned value, after)) :
    (eval model (fuel + 1) env joins (.invoke op next handler)).run before =
      (eval model fuel (env.extend value) joins next).run after := by
  simp [eval, h]
  rfl

example {g : Grade} (p : Prog g Int32) : Prog g.handled Int32 := p.getD 0
example {g : Grade} (p : Prog g Int32) : Prog g.handled (Option Int32) := p.attempt
example {g h : Grade} (p : Prog g Int32) (q : Prog h Int32) :
    Prog (g.handled.seq h) Int32 := p.orElse q

/-- error: Oria `do` grade mismatch -/
#guard_msgs(error, substring := true) in
example : Prog .pure Int32 := do
  Prog.fail

end Oria.Proofs.Failure
