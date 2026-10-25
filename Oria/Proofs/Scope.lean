module

import Oria.IR.Common.Scope

namespace Oria.Proofs.Scope

open Oria Oria.IR.Scope

universe u v w x

variable
    {ι : Type u} {o : Type v} {p : Type w} {q : Type x}
    {Γ Δ Ε : List ι} {a b c : ι}

/-- Repeated object types remain distinct variables because membership retains its position. -/
theorem repeated_types_have_distinct_indices (o : Type v) (a : ι) :
    let newest : Var o (a :: a :: Γ) a := Var.head
    let older : Var o (a :: a :: Γ) a :=
      (Var.head : Var o (a :: Γ) a).weaken a
    newest.index.val = 0 ∧ older.index.val = 1 ∧ newest ≠ older := by
  dsimp
  constructor
  · simp
  constructor
  · simp
  · intro equal
    have sameIndex := congrArg (fun x => x.index.val) equal
    simp at sameIndex

/-- The typed identity telescope enumerates both occurrences of a repeated type. -/
theorem identity_telescope_tracks_repeated_types (o : Type v) (a : ι) :
    let variables := Var.identity o ([a, a] : List ι)
    (variables.get 0).index.val = 0 ∧
      (variables.get 1).index.val = 1 := by
  simp

/-- Lifting through two binders fixes both binders and renames the older tail. -/
theorem liftMany_two_binders
    (ρ : Renaming o p Γ Δ)
    (x : Var o Γ c) :
    let newest : Var o (a :: b :: Γ) a := Var.head
    let next : Var o (a :: b :: Γ) b :=
      (Var.head : Var o (b :: Γ) b).weaken a
    (ρ.liftMany [a, b]) newest = (Var.head : Var p (a :: b :: Δ) a) ∧
      (ρ.liftMany [a, b]) next =
        (Var.head : Var p (b :: Δ) b).weaken a ∧
      (ρ.liftMany [a, b]) (x.weakenMany [a, b]) =
        (ρ x).weakenMany [a, b] := by
  dsimp only
  constructor
  · exact Renaming.lift_head _ _
  constructor
  · calc
      (ρ.lift b).lift a ((Var.head : Var o (b :: Γ) b).weaken a) =
          (ρ.lift b Var.head).weaken a :=
        Renaming.lift_weaken (ρ.lift b) a Var.head
      _ = (Var.head : Var p (b :: Δ) b).weaken a :=
        congrArg (fun y => y.weaken a) (Renaming.lift_head ρ b)
  · exact Renaming.liftMany_weakenMany ρ [a, b] x

/-- Multi-binder lifting distributes over composition. -/
theorem liftMany_two_binder_composition
    (ρ : Renaming o p Γ Δ)
    (σ : Renaming p q Δ Ε) :
    (σ.comp ρ).liftMany [a, b] =
      (σ.liftMany [a, b]).comp (ρ.liftMany [a, b]) := by
  simp

/-- A renaming's target owner and context still carry the source variable's exact type. -/
theorem target_membership_is_typed
    (ρ : Renaming o p Γ Δ) (x : Var o Γ a) :
    Δ.get (ρ x).index = a :=
  (ρ x).typeCorrect

/-- The left append embedding preserves every source position. -/
theorem appendLeft_preserves_index (x : Var o Γ a) :
    (Renaming.appendLeft o Γ Δ x).index.val = x.index.val :=
  Renaming.appendLeft_index x

/-- The right append embedding shifts by exactly the left telescope length. -/
theorem appendRight_shifts_index (x : Var o Δ a) :
    (Renaming.appendRight o Γ Δ x).index.val = x.index.val + Γ.length :=
  Renaming.appendRight_index x

end Oria.Proofs.Scope
