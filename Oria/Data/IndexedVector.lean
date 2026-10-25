module

import Init.Data.Vector.OfFn
import Init.Data.Vector.Lemmas

universe u v w

namespace Oria.Data

/-- A dependent vector backed by `Vector` with one erased alignment proof. -/
public structure IndexedVector {n : Nat} (f : Fin n → Type u) where
  private mk ::
  private data : Vector (Sigma f) n
  private aligned : ∀ i : Fin n, (data[i.1]).1 = i

namespace IndexedVector

public def ofFn {n : Nat} {f : Fin n → Type u}
    (build : (i : Fin n) → f i) : IndexedVector f :=
  ⟨Vector.ofFn (fun i => ⟨i, build i⟩), by intro i; simp⟩

private theorem aligned_of_ofFnM_ok
    {ε : Type v} {ι : Type w} {n : Nat} (f : ι → Type u)
    (tag : Fin n → ι) (build : (i : Fin n) → Except ε (f (tag i)))
    {data : Vector (Sigma f) n}
    (h : Vector.ofFnM (fun i =>
      (build i).map (fun x => (⟨tag i, x⟩ : Sigma f))) = .ok data) :
    ∀ i : Fin n, (data[i.1]).1 = tag i := by
  -- `Std` has `Vector.ofFnM`, but no monadic theorem preserving this dependent alignment.
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
      rw [Vector.ofFnM_succ] at h
      cases hp : Vector.ofFnM (fun i =>
          (build i.castSucc).map
            (fun x => (⟨tag i.castSucc, x⟩ : Sigma f))) with
      | error e =>
          rw [hp] at h
          change Except.error e = Except.ok data at h
          nomatch h
      | ok xs =>
          rw [hp] at h
          cases hl : build (Fin.last n) with
          | error e =>
              rw [hl] at h
              change Except.error e = Except.ok data at h
              nomatch h
          | ok xlast =>
              rw [hl] at h
              change Except.ok (xs.push (⟨tag (Fin.last n), xlast⟩ : Sigma f)) =
                Except.ok data at h
              injection h with hdata
              rw [← hdata]
              intro i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simp
              · simpa using ih (fun j : Fin n => tag j.castSucc)
                    (fun j : Fin n => build j.castSucc) hp j

public def ofFnM {ε : Type v} {n : Nat} {f : Fin n → Type u}
    (build : (i : Fin n) → Except ε (f i)) : Except ε (IndexedVector f) :=
  match result : Vector.ofFnM (fun i =>
      (build i).map fun x => (⟨i, x⟩ : Sigma f)) with
  | .error e => .error e
  | .ok data => .ok ⟨data, by
      simpa using aligned_of_ofFnM_ok f (fun i => i) build result⟩

@[expose] public def get
    {n : Nat} {f : Fin n → Type u} (xs : IndexedVector f) (i : Fin n) : f i :=
  private_decl% (cast (congrArg f (xs.aligned i)) xs.data[i.1].2)

private theorem get_eq {n : Nat} {f : Fin n → Type u}
    (xs : IndexedVector f) (i : Fin n) :
    xs.get i = cast (congrArg f (xs.aligned i)) xs.data[i.val].2 := by rfl

private theorem snd_congr {n : Nat} {f : Fin n → Type u} {i : Fin n}
    {a b : Sigma f} (ha : a.1 = i) (hb : b.1 = i) (h : a = b) :
    cast (congrArg f ha) a.2 = cast (congrArg f hb) b.2 := by
  cases h
  rfl

/-- Update one element with a value of its indexed type, preserving the vector's alignment. -/
public def set {n : Nat} {f : Fin n → Type u}
    (xs : IndexedVector f) (i : Fin n) (value : f i) : IndexedVector f := by
  refine ⟨xs.data.set i.val ⟨i, value⟩ i.isLt, ?_⟩
  intro j
  by_cases h : i.val = j.val
  · have same : i = j := Fin.ext h
    subst j
    simp
  · simpa [Vector.getElem_set, h] using xs.aligned j

@[simp] public theorem get_set_self {n : Nat} {f : Fin n → Type u}
    (xs : IndexedVector f) (i : Fin n) (value : f i) : (xs.set i value).get i = value := private_decl% (by
  rw [get_eq]
  exact snd_congr (b := ⟨i, value⟩) ((xs.set i value).aligned i) rfl (by simp [set]))

@[simp] public theorem get_set_ne {n : Nat} {f : Fin n → Type u}
    (xs : IndexedVector f) (i j : Fin n) (value : f i) (h : i ≠ j) :
    (xs.set i value).get j = xs.get j := private_decl% (by
  have different : i.val ≠ j.val := fun same => h (Fin.ext same)
  rw [get_eq, get_eq]
  exact snd_congr ((xs.set i value).aligned j) (xs.aligned j)
    (by simp [set, different]))

end IndexedVector

end Oria.Data
