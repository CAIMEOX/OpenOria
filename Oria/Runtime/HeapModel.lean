module

public import Std

namespace Oria.Runtime.HeapModel

/-- A decoded heap cell. `data` contains the constructor and scalar/native contents;
`edges` contains exactly the slots selected by its layout descriptor. -/
public structure Cell (A : Type) where
  data : A
  edges : List Nat
  deriving DecidableEq

public abbrev Heap (A : Type) := Nat → Option (Cell A)

public def Allocated (heap : Heap A) (p : Nat) : Prop :=
  ∃ cell, heap p = some cell

/-- Every stored pointer denotes an allocated cell. Addresses refer to one arena. -/
public def Closed (heap : Heap A) : Prop :=
  ∀ p cell, heap p = some cell → ∀ q ∈ cell.edges, Allocated heap q

public def RootsValid (heap : Heap A) (roots : List Nat) : Prop :=
  ∀ p ∈ roots, Allocated heap p

/-- Finite paths give the observations preserved by relocation and collection. -/
public inductive Reaches (heap : Heap A) : Nat → Nat → Prop where
  | refl (p) : Reaches heap p p
  | step {p q r cell} :
      Reaches heap p q → heap q = some cell → r ∈ cell.edges → Reaches heap p r

public def Reachable (heap : Heap A) (roots : List Nat) (p : Nat) : Prop :=
  ∃ root ∈ roots, Reaches heap root p

/-- Replacing one named root with a live persistent address preserves root validity.
The heap is shared unchanged by this operation. -/
public theorem publish_roots {heap : Heap A} {roots : List Nat}
    (valid : RootsValid heap roots) (slot p : Nat) (live : Allocated heap p) :
    RootsValid heap (roots.set slot p) := by
  intro q member
  rcases List.mem_or_eq_of_mem_set member with old | eq
  · exact valid q old
  · simpa [eq] using live

/-- The abstract effect of replacing a persistent Ref's payload. -/
public def write (heap : Heap A) (p : Nat) (cell : Cell A) : Heap A :=
  fun q => if q = p then some cell else heap q

public theorem write_retains_allocation {heap : Heap A} {p q : Nat} {cell : Cell A}
    (allocated : Allocated heap q) : Allocated (write heap p cell) q := by
  obtain ⟨old, found⟩ := allocated
  by_cases eq : q = p
  · exact ⟨cell, by simp [write, eq]⟩
  · exact ⟨old, by simp [write, eq, found]⟩

/-- Explicit Ref mutation preserves closure when every new edge is persistent and live. -/
public theorem write_closed {heap : Heap A} (closed : Closed heap)
    (p : Nat) (cell : Cell A)
    (valid : ∀ q ∈ cell.edges, Allocated heap q) :
    Closed (write heap p cell) := by
  intro q stored found r member
  by_cases eq : q = p
  · simp [write, eq] at found
    subst stored
    exact write_retains_allocation (valid r member)
  · simp [write, eq] at found
    exact write_retains_allocation (closed q stored found r member)

public theorem write_roots {heap : Heap A} {roots : List Nat}
    (valid : RootsValid heap roots) (p : Nat) (cell : Cell A) :
    RootsValid (write heap p cell) roots :=
  fun q member => write_retains_allocation (valid q member)

/-- Each source address has one reserved destination and one layout witness. -/
public abbrev Memo := Nat → Option (Nat × Nat)

public def Unique (memo : Memo) : Prop :=
  ∀ a b dst la lb, memo a = some (dst, la) → memo b = some (dst, lb) → a = b

/-- Reservation precedes traversal of the cell's outgoing edges. -/
public def reserve (memo : Memo) (src dst layout : Nat) : Memo :=
  fun p => if p = src then some (dst, layout) else memo p

public theorem reserve_unique {memo : Memo} (unique : Unique memo)
    (src dst layout : Nat) (fresh : ∀ p l, memo p ≠ some (dst, l)) :
    Unique (reserve memo src dst layout) := by
  intro a b d la lb ha hb
  by_cases ea : a = src <;> by_cases eb : b = src
  · exact ea.trans eb.symm
  · subst a
    simp [reserve, eb] at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    exact False.elim (fresh b lb hb)
  · subst b
    simp [reserve, ea] at ha hb
    obtain ⟨rfl, rfl⟩ := hb
    exact False.elim (fresh a la ha)
  · exact unique a b d la lb (by simpa [reserve, ea] using ha) (by simpa [reserve, eb] using hb)

/-- A completed promotion preserves decoded contents under its reserved address map.
Existing persistent cells may use the identity mapping. Layout metadata is supplied
by the compiler's promotion plan and is separate from decoded contents. -/
public structure Promotion (source target : Heap A) where
  address : Nat → Nat
  injective : Function.Injective address
  copied : ∀ p cell, source p = some cell →
    target (address p) = some ⟨cell.data, cell.edges.map address⟩

public theorem Promotion.value {source target : Heap A} (copy : Promotion source target)
    {p : Nat} {cell : Cell A} (found : source p = some cell) :
    (target (copy.address p)).map Cell.data = some cell.data := by
  rw [copy.copied p cell found]
  rfl

/-- Aliases stay aliases; distinct source objects retain distinct identities. -/
public theorem Promotion.sharing {source target : Heap A} (copy : Promotion source target)
    (p q : Nat) : copy.address p = copy.address q ↔ p = q :=
  ⟨fun h => copy.injective h, congrArg copy.address⟩

public theorem Promotion.path {source target : Heap A} (copy : Promotion source target)
    {p q : Nat} (path : Reaches source p q) :
    Reaches target (copy.address p) (copy.address q) := by
  induction path with
  | refl => exact .refl _
  | step _ found member ih =>
      exact .step ih (copy.copied _ _ found) (List.mem_map.mpr ⟨_, member, rfl⟩)

/-- The mark worklist's completion condition: every root is marked, and every marked
cell's pointer slots have been scanned. Marks may conservatively include extra cells. -/
public def MarkedClosed (heap : Heap A) (roots : List Nat) (marked : Nat → Bool) : Prop :=
  (∀ p ∈ roots, marked p = true) ∧
    (∀ p cell, marked p = true → heap p = some cell →
      ∀ q ∈ cell.edges, marked q = true)

/-- The marker retains one bit per address and a worklist of discovered pointers. -/
public structure Mark where
  marked : Nat → Bool
  todo : List Nat

public def Mark.Covered (s : Mark) (p : Nat) : Prop :=
  s.marked p = true ∨ p ∈ s.todo

/-- Roots and outgoing edges of marked cells have either been visited or queued. -/
public def Mark.Invariant (s : Mark) (heap : Heap A) (roots : List Nat) : Prop :=
  (∀ p ∈ roots, s.Covered p) ∧
    (∀ p cell, s.marked p = true → heap p = some cell →
      ∀ q ∈ cell.edges, s.Covered q)

public theorem Mark.initial (heap : Heap A) (roots : List Nat) :
    (Mark.mk (fun _ => false) roots).Invariant heap roots := by
  constructor
  · intro p member; exact .inr member
  · intro p cell marked; contradiction

/-- Reserve the mark before enqueueing outgoing edges, including cyclic references. -/
public def Mark.scan (marked : Nat → Bool) (p : Nat) (cell : Cell A) (tail : List Nat) : Mark :=
  ⟨fun q => q == p || marked q, cell.edges ++ tail⟩

public theorem Mark.scan_preserves {heap : Heap A} {roots : List Nat}
    {marked : Nat → Bool} {p : Nat} {tail : List Nat} {cell : Cell A}
    (invariant : (Mark.mk marked (p :: tail)).Invariant heap roots)
    (found : heap p = some cell) :
    (scan marked p cell tail).Invariant heap roots := by
  have covered : ∀ q, (Mark.mk marked (p :: tail)).Covered q →
      (scan marked p cell tail).Covered q := by
    intro q known
    rcases known with old | queued
    · change marked q = true at old
      exact .inl (by simp [scan, old])
    · rcases List.mem_cons.mp queued with same | queued
      · exact .inl (by simp [scan, same])
      · exact .inr (List.mem_append_right _ queued)
  constructor
  · intro q member; exact covered q (invariant.1 q member)
  · intro q obj markedNow lookup r edge
    have cases : q = p ∨ marked q = true := by simpa [scan] using markedNow
    rcases cases with same | old
    · subst q
      have eq : obj = cell := Option.some.inj (lookup.symm.trans found)
      subst obj
      exact .inr (List.mem_append_left _ edge)
    · exact covered r (invariant.2 q obj old lookup r edge)

public theorem Mark.skip_preserves {heap : Heap A} {roots : List Nat}
    {marked : Nat → Bool} {p : Nat} {tail : List Nat}
    (invariant : (Mark.mk marked (p :: tail)).Invariant heap roots)
    (visited : marked p = true) :
    (Mark.mk marked tail).Invariant heap roots := by
  have covered : ∀ q, (Mark.mk marked (p :: tail)).Covered q →
      (Mark.mk marked tail).Covered q := by
    intro q known
    rcases known with old | queued
    · exact .inl old
    · rcases List.mem_cons.mp queued with same | queued
      · exact .inl (same ▸ visited)
      · exact .inr queued
  exact ⟨fun q member => covered q (invariant.1 q member),
    fun q cell mark found r edge => covered r (invariant.2 q cell mark found r edge)⟩

public theorem Mark.finished {heap : Heap A} {roots : List Nat} {marked : Nat → Bool}
    (invariant : (Mark.mk marked []).Invariant heap roots) : MarkedClosed heap roots marked := by
  simpa [Invariant, Covered, MarkedClosed] using invariant

public theorem reachable_marked {heap : Heap A} {roots : List Nat} {marked : Nat → Bool}
    (closed : MarkedClosed heap roots marked) {p : Nat}
    (reachable : Reachable heap roots p) : marked p = true := by
  obtain ⟨r, member, path⟩ := reachable
  induction path with
  | refl => exact closed.1 _ member
  | step _ found edge ih => exact closed.2 _ _ ih found _ edge

/-- Sweeping leaves retained addresses stable and releases every unmarked cell. -/
public def sweep (heap : Heap A) (marked : Nat → Bool) : Heap A :=
  fun p => if marked p then heap p else none

/-- Every reachable cell keeps all decoded contents at the same address. -/
public theorem sweep_preserves {heap : Heap A} {roots : List Nat} {marked : Nat → Bool}
    (closed : MarkedClosed heap roots marked) {p : Nat}
    (reachable : Reachable heap roots p) : sweep heap marked p = heap p := by
  simp [sweep, reachable_marked closed reachable]

public theorem sweep_closed {heap : Heap A} {roots : List Nat} {marked : Nat → Bool}
    (heapClosed : Closed heap) (markedClosed : MarkedClosed heap roots marked) :
    Closed (sweep heap marked) := by
  intro p cell found q member
  have mark : marked p = true := by
    by_cases h : marked p = true
    · exact h
    · simp [sweep, h] at found
  have original : heap p = some cell := by simpa [sweep, mark] using found
  have child := markedClosed.2 p cell mark original q member
  obtain ⟨old, found⟩ := heapClosed p cell original q member
  exact ⟨old, by simpa [sweep, child] using found⟩

public theorem sweep_roots {heap : Heap A} {roots : List Nat} {marked : Nat → Bool}
    (valid : RootsValid heap roots) (closed : MarkedClosed heap roots marked) :
    RootsValid (sweep heap marked) roots := by
  intro p member
  change ∃ cell, sweep heap marked p = some cell
  rw [sweep_preserves closed ⟨p, member, .refl p⟩]
  exact valid p member

end Oria.Runtime.HeapModel
