module

public import Oria.Compiler.RegAlloc.Location
public import Oria.Compiler.RegAlloc.Check

namespace Oria.RegAlloc

private structure Candidate where
  index : Nat
  range : Range
  deriving Repr

private structure Active (registers : Nat) where
  index : Nat
  range : Range
  home : Fin registers
  deriving Repr

private structure StackActive where
  range : Range
  home : Nat
  deriving Repr

private inductive Placement (registers : Nat) where
  | reg : Fin registers → Placement registers
  | spill : Placement registers
  deriving Repr

private inductive RawHome (registers : Nat) where
  | reg : Fin registers → RawHome registers
  | stack : Nat → RawHome registers
  deriving Repr

private def candidates (ranges : Array (Option Range)) : Option (List Candidate) :=
  let n := ranges.size
  (List.finRange n).foldr (fun i result => do
    let rest ← result
    match ranges[i.val] with
    | none => pure rest
    | some range =>
        if _h : range.start < range.stop then
          pure ({ index := i.val, range } :: rest)
        else
          none) (some [])

private def before (left right : Candidate) : Bool :=
  left.range.start < right.range.start ||
    (left.range.start == right.range.start && left.index < right.index)

private def sameRegister
    {registers : Nat} (register : Fin registers) :
    Active registers → Bool
  | ⟨_, _, other⟩ => register == other

private def freeRegisters
    (registers : Nat) (active : List (Active registers)) : List (Fin registers) :=
  (List.finRange registers).filter fun register =>
    !active.any (sameRegister register)

private def chooseRegister {registers : Nat}
    (cost : Nat → Fin registers → Nat) (index : Nat) :
    List (Fin registers) → Option (Fin registers)
  | [] => none
  | first :: rest =>
      some <| rest.foldl (fun best register =>
        let bestCost := cost index best
        let registerCost := cost index register
        if registerCost < bestCost ||
            (registerCost == bestCost && register.val < best.val) then
          register
        else
          best) first

private def farther {registers : Nat}
    (left right : Active registers) : Bool :=
  left.range.stop > right.range.stop ||
    (left.range.stop == right.range.stop && left.index > right.index)

private def farthestRegister {registers : Nat}
    (active : List (Active registers)) : Option (Active registers) :=
  active.foldl (fun best current =>
    match best with
    | none => some current
    | some previous => if farther current previous then some current else some previous) none

private def putPlacement {registers : Nat}
    (placements : Array (Option (Placement registers)))
    (index : Nat) (placement : Placement registers) :
    Array (Option (Placement registers)) :=
  placements.set! index (some placement)

private def scanRegisters {registers : Nat}
    (cost : Nat → Fin registers → Nat)
    (pending : List Candidate)
    (active : List (Active registers))
    (placements : Array (Option (Placement registers))) :
    Option (Array (Option (Placement registers))) :=
  match pending with
  | [] => some placements
  | candidate :: rest =>
      let active := active.filter (·.range.stop > candidate.range.start)
      match chooseRegister cost candidate.index (freeRegisters registers active) with
      | some register =>
          scanRegisters cost rest
            ({ index := candidate.index, range := candidate.range, home := register } :: active)
            (putPlacement placements candidate.index (.reg register))
      | none =>
          match farthestRegister active with
          | some victim =>
              if victim.range.stop ≤ candidate.range.stop then
                scanRegisters cost rest active
                  (putPlacement placements candidate.index .spill)
              else
                scanRegisters cost rest
                  ({ index := candidate.index, range := candidate.range, home := victim.home } ::
                    active.filter (·.index != victim.index))
                  (putPlacement (putPlacement placements victim.index .spill)
                    candidate.index (.reg victim.home))
          | none =>
              scanRegisters cost rest active
                (putPlacement placements candidate.index .spill)

private def sameStack (slot : Nat) : StackActive → Bool
  | ⟨_, other⟩ => slot == other

private def expireStacks (start : Nat) : List StackActive → List StackActive
  | [] => []
  | active :: rest =>
      if active.range.stop ≤ start then expireStacks start rest
      else active :: expireStacks start rest

private def chooseStack (active : List StackActive) : Nat :=
  let rec search (fuel slot : Nat) : Nat :=
    match fuel with
    | 0 => slot
    | fuel + 1 =>
        if active.any (sameStack slot) then search fuel (slot + 1) else slot
  search (active.length + 1) 0

private def putHome {registers : Nat}
    (homes : Array (Option (RawHome registers)))
    (index : Nat) (home : RawHome registers) :
    Array (Option (RawHome registers)) :=
  homes.set! index (some home)

private def spillCandidates {registers : Nat}
    (placements : Array (Option (Placement registers)))
    (all : List Candidate) : List Candidate :=
  all.filter fun candidate =>
    match placements[candidate.index]? with
    | some (some .spill) => true
    | _ => false

private def scanStacks {registers : Nat}
    (pending : List Candidate)
    (active : List StackActive)
    (homes : Array (Option (RawHome registers)))
    (slots : Nat) :
    Array (Option (RawHome registers)) × Nat :=
  match pending with
  | [] => (homes, slots)
  | candidate :: rest =>
      let active := expireStacks candidate.range.start active
      let slot := chooseStack active
      let slots := max slots (slot + 1)
      scanStacks rest
        ({ range := candidate.range, home := slot } :: active)
        (putHome homes candidate.index (.stack slot)) slots

private def toVector {registers slots : Nat}
    (homes : Array (Option (Loc registers slots))) (size : Nat) :
    Vector (Option (Loc registers slots)) size :=
  Vector.ofFn fun i => homes[i.val]?.getD none

@[expose] public def allocate
    (registers : Nat) (ranges : Array (Option Range))
    (cost : Nat → Fin registers → Nat := fun _ _ => 0) :
    Option (Assignment registers ranges) := private_decl% (do
    let pending ← candidates ranges
    let ordered := pending.mergeSort before
    let placements ← scanRegisters cost ordered [] (Array.replicate ranges.size none)
    let (rawHomes, slots) := scanStacks (spillCandidates placements ordered) []
      (placements.map fun placement =>
        match placement with
        | some (.reg register) => some (.reg register)
        | some .spill | none => none) 0
    let homes := rawHomes.map fun home =>
      match home with
      | none => none
      | some (.reg register) => some (.reg register)
      | some (.stack slot) =>
          if h : slot < slots then some (.stack ⟨slot, h⟩) else none
    let homes := toVector homes ranges.size
    if checked : validate ranges slots homes = true then
      some ⟨slots, homes, valid_of_validate ranges slots homes checked⟩
    else
      none)

end Oria.RegAlloc
