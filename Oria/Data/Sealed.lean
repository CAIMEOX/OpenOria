module

namespace Oria

/-
Lean's module compiler requires a uniform compilation type across import modes.
An opaque existential keeps that type uniform while its private operations retain
the representation. This follows the opaque-carrier idiom in Init.Dynamic and
Lean.Environment; the codecs here are total and carry their round-trip equation.
-/
private structure Carrier (K : Type u) (A : Type v) where
  type : K → Type v
  wrap : (k : K) → A → type k
  unwrap : (k : K) → type k → A
  roundTrip : ∀ k a, unwrap k (wrap k a) = a

private opaque carrier (K : Type u) (A : Type v) : Carrier K A :=
  ⟨fun _ => A, fun _ => id, fun _ => id, fun _ _ => rfl⟩

/-- An abstract carrier indexed by a semantic identity. Its representation operations
are available only to modules that explicitly import the implementation. -/
public def Sealed {K : Type u} (k : K) (A : Type v) : Type v :=
  (carrier K A).type k

set_option backward.privateInPublic true in
@[noinline] private def Sealed.mk {K : Type u} {k : K} {A : Type v} (a : A) : Sealed k A :=
  (carrier K A).wrap k a

set_option backward.privateInPublic true in
@[noinline] private def Sealed.get {K : Type u} {k : K} {A : Type v} (a : Sealed k A) : A :=
  (carrier K A).unwrap k a

private theorem Sealed.get_mk {K : Type u} {k : K} {A : Type v} (a : A) :
    (Sealed.mk a : Sealed k A).get = a :=
  (carrier K A).roundTrip k a

end Oria
