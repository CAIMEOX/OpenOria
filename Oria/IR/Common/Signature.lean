module

public import Oria.Effect.Grade
public import Oria.IR.Common.Type

namespace Oria

universe u v w x y

public structure Signature where
  args : List ObjTy
  result : ObjTy
  grade : Grade
  deriving BEq, DecidableEq, Hashable, Repr

/-- A heterogeneous sequence whose element family is indexed by a type-level list. -/
public inductive Args {ι : Type u} (f : ι → Type v) : List ι → Type (max u v) where
  | nil : Args f []
  | cons {a : ι} {as : List ι} : f a → Args f as → Args f (a :: as)

namespace Args

@[expose] public def length {ι : Type u} {f : ι → Type v} {as : List ι} : Args f as → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

@[simp] public theorem length_eq {ι : Type u} {f : ι → Type v} {as : List ι}
    (xs : Args f as) : xs.length = as.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [length, ih]

@[expose] public def map {ι : Type u} {f : ι → Type v} {g : ι → Type w} {as : List ι}
    (η : ∀ {a}, f a → g a) : Args f as → Args g as
  | .nil => .nil
  | .cons value rest => .cons (η value) (rest.map η)

/-- Concatenate two indexed telescopes while preserving their element family. -/
@[expose] public def append {ι : Type u} {f : ι → Type v} {as bs : List ι} :
    Args f as → Args f bs → Args f (as ++ bs)
  | .nil, right => right
  | .cons value rest, right => .cons value (rest.append right)

/-- Construct an indexed telescope from its total finite lookup function. -/
@[expose] public def tabulate
    {ι : Type u} {f : ι → Type v}
    (as : List ι)
    (value : (i : Fin as.length) → f (as.get i)) : Args f as :=
  match as with
  | [] => .nil
  | _ :: rest =>
      .cons (value ⟨0, by simp⟩)
        (tabulate rest fun i => value ⟨i.val + 1, by simp [i.isLt]⟩)

@[simp] public theorem length_append {ι : Type u} {f : ι → Type v} {as bs : List ι}
    (left : Args f as) (right : Args f bs) :
    (left.append right).length = left.length + right.length := by
  rw [length_eq, length_eq, length_eq]
  simp

private def splitAt {ι : Type u} {f : ι → Type v} {bs : List ι} :
    (as : List ι) → Args f (as ++ bs) → Args f as × Args f bs
  | [], values => (.nil, values)
  | _ :: rest, .cons value tail =>
      let (left, right) := splitAt rest tail
      (.cons value left, right)

@[expose] public def split {ι : Type u} {f : ι → Type v} {as bs : List ι}
    (values : Args f (as ++ bs)) : Args f as × Args f bs :=
  private_decl% splitAt as values

private theorem splitAt_append {ι : Type u} {f : ι → Type v} {as bs : List ι}
    (left : Args f as) (right : Args f bs) :
    splitAt as (left.append right) = (left, right) := by
  induction left with
  | nil => rfl
  | cons value rest induction => simp only [append, splitAt]; rw [induction]

@[simp] public theorem split_append {ι : Type u} {f : ι → Type v} {as bs : List ι}
    (left : Args f as) (right : Args f bs) :
    (left.append right).split = (left, right) :=
  private_decl% splitAt_append left right

/-- Dependent lookup retaining the element index from the type-level list. -/
@[expose] public def get {ι : Type u} {f : ι → Type v} {as : List ι} :
    (xs : Args f as) → (i : Fin as.length) → f (as.get i)
  | .cons value _, ⟨0, _⟩ => value
  | .cons _ rest, ⟨i + 1, inBounds⟩ => rest.get ⟨i, Nat.lt_of_succ_lt_succ inBounds⟩

@[simp] public theorem get_map {ι : Type u} {f : ι → Type v} {as : List ι} {g : ι → Type w}
    (η : ∀ {a}, f a → g a) (xs : Args f as) (i : Fin as.length) :
    (xs.map η).get i = η (xs.get i) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons value rest induction =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact induction j

@[simp] public theorem get_tabulate
    {ι : Type u} {f : ι → Type v}
    (as : List ι)
    (value : (i : Fin as.length) → f (as.get i))
    (i : Fin as.length) : (tabulate as value).get i = value i := by
  induction as with
  | nil => exact Fin.elim0 i
  | cons head rest induction =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact induction _ j

public theorem ext
    {ι : Type u} {f : ι → Type v} {as : List ι}
    (left right : Args f as)
    (same : ∀ i : Fin as.length, left.get i = right.get i) : left = right := by
  induction left with
  | nil => cases right; rfl
  | @cons a as value rest induction =>
      cases right with
      | cons other tail =>
          have head := same ⟨0, by simp⟩
          have remaining : ∀ i : Fin as.length,
              rest.get i = tail.get i := fun i => same ⟨i.val + 1, by
                simp [i.isLt]⟩
          cases head
          rw [induction tail remaining]

/-- Transform an indexed telescope from left to right while threading a continuation. -/
public def traverseK
    {ι : Type u} {f : ι → Type v} {g : ι → Type x} {as : List ι}
    {r : Type w}
    (visit : ∀ {a}, f a → (g a → r) → r)
    (xs : Args f as)
    (next : Args g as → r) : r :=
  match xs with
  | .nil => next .nil
  | .cons value rest =>
      visit value fun transformed =>
        rest.traverseK visit fun transformedRest =>
          next (.cons transformed transformedRest)

public theorem traverseK_pure
    {ι : Type u} {f : ι → Type v} {g : ι → Type x} {as : List ι} {r : Type w}
    (η : ∀ {a}, f a → g a)
    (xs : Args f as)
    (next : Args g as → r) :
    xs.traverseK (fun value k => k (η value)) next =
      next (xs.map η) := by
  induction xs with
  | nil => rfl
  | cons value rest induction =>
      simp only [traverseK, map]
      exact induction _

public def All {ι : Type u} {f : ι → Type v} {as : List ι}
    (p : ∀ {a}, f a → Prop) : Args f as → Prop
  | .nil => True
  | .cons value rest => p value ∧ rest.All p

/-- Proof-relevant evidence for every value in an indexed telescope. -/
@[expose] public def AllT
    {i : Type u} {f : i → Type v} {as : List i}
    (p : ∀ {a}, f a → Type x) : Args f as → Type (max u v x)
  | .nil => PUnit
  | .cons value rest => p value × rest.AllT p

namespace AllT

@[expose] public def map
    {i : Type u} {f : i → Type v} {as : List i}
    {p : ∀ {a}, f a → Type w} {q : ∀ {a}, f a → Type x}
    (transform : ∀ {a} (value : f a), p value → q value) :
    (xs : Args f as) → xs.AllT p → xs.AllT q
  | .nil, _ => PUnit.unit
  | .cons value rest, evidence =>
      (transform value evidence.1, map transform rest evidence.2)

end AllT

/-- Transform an indexed telescope while consuming proof-relevant evidence at each value. -/
@[expose] public def traverseKAllT
    {i : Type u} {f : i → Type v} {g : i → Type x}
    {as : List i} {p : ∀ {a}, f a → Type w}
    {r : Type y}
    (visit : ∀ {a} (value : f a), p value → (g a → r) → r)
    (xs : Args f as)
    (evidence : xs.AllT p)
    (next : Args g as → r) : r :=
  match xs with
  | .nil => next .nil
  | .cons value rest =>
      visit value evidence.1 fun transformed =>
        rest.traverseKAllT visit evidence.2 fun transformedRest =>
          next (.cons transformed transformedRest)

public def proveAll
    {m : Type → Type u}
    {ι : Type v} {f : ι → Type w} {p : ∀ {a}, f a → Prop} {as : List ι}
    [Monad m]
    (prove : ∀ {a} (value : f a), m (PLift (p value))) :
    (xs : Args f as) → m (PLift (xs.All p))
  | .nil => pure ⟨True.intro⟩
  | .cons value rest => do
      let ⟨valueProof⟩ ← prove value
      let ⟨restProof⟩ ← rest.proveAll prove
      pure ⟨⟨valueProof, restProof⟩⟩

@[expose] public def foldl {b : Sort u} {ι : Type v} {f : ι → Type w} {as : List ι}
    (step : ∀ {a}, b → f a → b) : b → Args f as → b
  | result, .nil => result
  | result, .cons value rest => rest.foldl step (step result value)

@[simp] public theorem map_id {ι : Type u} {f : ι → Type v} {as : List ι} (xs : Args f as) :
    xs.map (fun value => value) = xs := by
  induction xs with
  | nil => rfl
  | cons value rest induction => simp [map, induction]

public theorem map_comp {ι : Type u} {f : ι → Type v} {as : List ι}
    {g : ι → Type w} {h : ι → Type x}
    (left : ∀ {a}, f a → g a)
    (right : ∀ {a}, g a → h a)
    (xs : Args f as) :
    (xs.map left).map right = xs.map (fun value => right (left value)) := by
  induction xs with
  | nil => rfl
  | cons value rest induction => simp [map, induction]

end Args

end Oria
