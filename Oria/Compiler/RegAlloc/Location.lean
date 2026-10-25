module

namespace Oria.RegAlloc

/-- A half-open lifetime in the local instruction event order. -/
public structure Range where
  start : Nat
  stop : Nat
  deriving BEq, DecidableEq, Repr

namespace Range

@[expose] public def valid (r : Range) : Prop := r.start < r.stop

@[expose] public def overlaps (left right : Range) : Prop :=
  left.start < right.stop ∧ right.start < left.stop

@[expose] public def contains (r : Range) (point : Nat) : Prop :=
  r.start ≤ point ∧ point < r.stop

@[simp] public theorem overlaps_comm (left right : Range) :
    overlaps left right ↔ overlaps right left := by
  simp only [overlaps, and_comm]

@[simp] public theorem not_overlaps_of_stop_le_start
    {left right : Range} (h : left.stop ≤ right.start) :
    ¬overlaps left right := by
  intro overlap
  exact (Nat.not_lt_of_ge h) overlap.2

end Range

/-- A physical home in a bounded register file and a finite stack frame. -/
public inductive Loc (registers slots : Nat) where
  | reg : Fin registers → Loc registers slots
  | stack : Fin slots → Loc registers slots
  deriving DecidableEq, Repr

public instance : BEq (Loc registers slots) where
  beq left right := decide (left = right)

public instance : LawfulBEq (Loc registers slots) where
  rfl := by
    intro location
    cases location <;> simp
  eq_of_beq := by
    intro left right equal
    exact of_decide_eq_true equal

namespace Loc

@[simp] public theorem reg_inj {a b : Fin registers} :
    (Loc.reg a : Loc registers slots) = .reg b ↔ a = b := by
  simp

@[simp] public theorem stack_inj {a b : Fin slots} :
    (Loc.stack a : Loc registers slots) = .stack b ↔ a = b := by
  simp

@[simp] public theorem reg_ne_stack {a : Fin registers} {b : Fin slots} :
    (Loc.reg a : Loc registers slots) ≠ .stack b := by
  intro h
  cases h

end Loc

/-!
`Valid` is deliberately a flat certificate.  The allocator only needs to
expose the homes and the number of stack slots; consumers can inspect one
property instead of depending on an intermediate allocation trace.
-/
public structure Valid
    (ranges : Array (Option Range))
    (slots : Nat)
    (homes : Vector (Option (Loc registers slots)) ranges.size) : Prop where
  present : ∀ i : Fin ranges.size,
    (ranges[i.1] = none) ↔ (homes.get i = none)
  disjoint : ∀ (i j : Fin ranges.size) (left right : Range)
    (leftHome rightHome : Loc registers slots),
    i ≠ j → ranges[i.1] = some left → ranges[j.1] = some right →
    homes.get i = some leftHome → homes.get j = some rightHome →
    leftHome = rightHome → ¬Range.overlaps left right

public structure Assignment (registers : Nat) (ranges : Array (Option Range)) where
  slots : Nat
  homes : Vector (Option (Loc registers slots)) ranges.size
  valid : Valid ranges slots homes

namespace Assignment

@[simp] public theorem absent_home
    (assignment : Assignment registers ranges) (i : Fin ranges.size)
    (h : ranges[i.1] = none) : assignment.homes.get i = none := by
  exact (assignment.valid.present i).mp h

@[simp] public theorem present_home
    (assignment : Assignment registers ranges) (i : Fin ranges.size)
    (r : Range) (h : ranges[i.1] = some r) : assignment.homes.get i ≠ none := by
  intro absent
  have absentRange : ranges[i.1] = none := (assignment.valid.present i).mpr absent
  rw [h] at absentRange
  simp at absentRange

end Assignment

end Oria.RegAlloc
