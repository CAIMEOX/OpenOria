module

public import Oria.Compiler.RegAlloc.Location

namespace Oria.RegAlloc

private def presenceAt {registers slots : Nat}
    (ranges : Array (Option Range))
    (homes : Vector (Option (Loc registers slots)) ranges.size)
    (i : Fin ranges.size) : Bool :=
  decide (ranges[i.val] = none ↔ homes.get i = none)

private def collisionAt {registers slots : Nat}
    (ranges : Array (Option Range))
    (homes : Vector (Option (Loc registers slots)) ranges.size)
    (i j : Fin ranges.size) : Bool :=
  if i == j then
    true
  else
    match ranges[i.val], ranges[j.val], homes.get i, homes.get j with
    | some left, some right, some leftHome, some rightHome =>
        if leftHome == rightHome then
          !(decide (left.start < right.stop ∧ right.start < left.stop))
        else
          true
    | _, _, _, _ => true

private def allPresence {registers slots : Nat}
    (ranges : Array (Option Range))
    (homes : Vector (Option (Loc registers slots)) ranges.size) : Bool :=
  (List.finRange ranges.size).all (presenceAt ranges homes)

private def allCollisions {registers slots : Nat}
    (ranges : Array (Option Range))
    (homes : Vector (Option (Loc registers slots)) ranges.size) : Bool :=
  (List.finRange ranges.size).all fun i =>
    (List.finRange ranges.size).all (collisionAt ranges homes i)

/- Executable form of the flat placement certificate. -/
public def validate {registers : Nat}
    (ranges : Array (Option Range))
    (slots : Nat)
    (homes : Vector (Option (Loc registers slots)) ranges.size) : Bool :=
  allPresence ranges homes && allCollisions ranges homes

/-- A successful executable check produces the proposition consumed by backends. -/
public theorem valid_of_validate {registers : Nat}
    (ranges : Array (Option Range))
    (slots : Nat)
    (homes : Vector (Option (Loc registers slots)) ranges.size)
    (checked : validate ranges slots homes = true) :
    Valid ranges slots homes := by
  have parts : allPresence ranges homes = true ∧ allCollisions ranges homes = true := by
    simpa [validate] using checked
  constructor
  · intro i
    have every := (List.all_eq_true.mp parts.1) i (List.mem_finRange i)
    exact of_decide_eq_true every
  · intro i j left right leftHome rightHome different leftRange rightRange
      leftHomeAt rightHomeAt sameHome
    have everyI := (List.all_eq_true.mp parts.2) i (List.mem_finRange i)
    have everyJ := (List.all_eq_true.mp everyI j (List.mem_finRange j))
    have different' : (i == j) = false := by simp [different]
    rw [collisionAt, different'] at everyJ
    simp [leftRange, rightRange, leftHomeAt, rightHomeAt, sameHome] at everyJ
    have noOverlap : ¬(left.start < right.stop ∧ right.start < left.stop) := by
      intro overlap
      rcases overlap with ⟨leftBeforeRight, rightBeforeLeft⟩
      rcases everyJ with separated | separated <;> omega
    intro overlap
    exact noOverlap overlap

end Oria.RegAlloc
