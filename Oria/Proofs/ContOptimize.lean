module

import all Oria.Compiler.Optimize.Cont
import all Oria.IR.Cont.Definition
import all Oria.IR.Common.Scope
import Oria.IR.Cont.Pretty
meta import Oria.Compiler.Optimize.Cont
meta import Oria.IR.Cont.Pretty

namespace Oria.Proofs.ContOptimize

open Oria Oria.IR Oria.IR.Cont

private def copied (x : Int32) : Def ⟨[], .i32, .pure⟩ :=
  Def.build fun _ => .letOp (.copy (.i32 x))
    (.letOp (.copy (.local .head)) (.ret (.local .head)))

theorem copies (x : Int32) :
    (Optimize.Cont.run (copied x)).computation = .ret (.i32 x) := rfl

private def choice (x y : Int32) : Def ⟨[], .i32, .pure⟩ :=
  Def.build fun _ => .branch (.bool true) (.ret (.i32 x)) (.ret (.i32 y))

theorem constantBranch (x y : Int32) :
    (Optimize.Cont.run (choice x y)).computation = .ret (.i32 x) := rfl

private def negated (x : Int32) : Def ⟨[], .i32, .pure⟩ :=
  Def.build fun _ => .letOp (.unary .neg (.i32 x)) (.ret (.local .head))

theorem fold_negation (x : Int32) :
    (Optimize.Cont.run (negated x)).computation = .ret (.i32 (-x)) := rfl

private def divided (x y : Int32) : Def ⟨[], .i32, .failure⟩ :=
  Def.build fun _ => .invoke (.division (.i32 x) (.i32 y)) (.ret (.local .head)) .fail

theorem fold_division (x y : Int32) :
    (Optimize.Cont.run (divided x y)).computation =
      match I32.divide x y with
      | some value => .ret (.i32 value)
      | none => .fail := by
  change ((match I32.divide x y with
    | some value => .ret (.i32 value)
    | none => .fail) : Comp [] .i32 []) = _
  rfl

private def identities : Def ⟨[.i32], .i32, .pure⟩ :=
  Def.build fun _ => .letOp (.binary .add (.local .head) (.i32 0))
    (.letOp (.binary .mul (.local .head) (.i32 1)) (.ret (.local .head)))

theorem simplify_identities :
    (Optimize.Cont.run identities).computation = .ret (.local .head) := rfl

theorem identities_semantics (x : Int32) : (x + 0) * 1 = x := by simp

theorem bit_selection (x : Int32) (h : x = 0 ∨ x = 1) :
    (if x = 1 then (1 : Int32) else 0) = x := by rcases h with rfl | rfl <;> decide

private def wrapped (x : Int32) : Def ⟨[], .i32, .pure⟩ :=
  Def.build fun _ => .letOp (.construct .some (.cons (.i32 x) .nil))
    (.switch (.local .head)
      (.cons .none (.ret (.i32 0))
        (.cons .some (.ret (.local .head)) .nil)))

/- Constructor elimination exposes an unused object binding to physical demand pruning. -/
#guard (Optimize.Cont.run (wrapped 7)).pretty 100 =
  "fn () -> I32 !{req=0, eff=0} {\n  let %0 : Option[I32] <- construct Option.some 7\n  return 7\n}"

end Oria.Proofs.ContOptimize
