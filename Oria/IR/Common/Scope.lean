module

public import Oria.IR.Common.Signature

namespace Oria.IR.Scope

universe u v w x y z

variable
    {ι : Type u}
    {o : Type v} {p : Type w} {q : Type x} {r : Type y}
    {Γ Δ Ε Ζ : List ι} {a b : ι}

/--
Lean and `Std` provide `Fin`, `List.get`, and ordinary function composition, but no dependent
list membership that retains `Γ.get i = a`, nor its total type-preserving binder lifting. This
module packages those missing pieces as the shared scope kernel for Oria IRs. Its single phantom
owner is the nominal boundary; clients may combine finer identities in their own opaque owner type.
-/
public structure Var (o : Type v) {ι : Type u} (Γ : List ι) (a : ι) where
  private mk ::
  index : Fin Γ.length
  typeCorrect : Γ.get index = a

namespace Var

@[expose] public def ofIndex (o : Type v) (i : Fin Γ.length) : Var o Γ (Γ.get i) :=
  private_decl% ⟨i, rfl⟩

@[simp] public theorem ofIndex_index (i : Fin Γ.length) :
    (ofIndex o i).index = i :=
  private_decl% (by rfl)

/-- The most recently bound variable. -/
@[expose] public def head : Var o (a :: Γ) a :=
  private_decl% ⟨0, rfl⟩

/-- Shift a variable beneath one new binder. -/
@[expose] public def weaken (x : Var o Γ a) (b : ι) : Var o (b :: Γ) a :=
  private_decl% ⟨x.index.succ, by
    simpa only [List.get_cons_succ'] using x.typeCorrect⟩

/-- Shift a variable beneath a telescope of new binders. -/
@[expose] public def weakenMany (x : Var o Γ a) : (Δ : List ι) → Var o (Δ ++ Γ) a
  | [] => x
  | b :: Δ => (x.weakenMany Δ).weaken b

/-- The typed identity telescope for a context. -/
@[expose] public def identity (o : Type v) (Γ : List ι) : Args (Var o Γ) Γ :=
  Args.tabulate Γ (ofIndex o)

/-- Read one heterogeneous telescope at a statically type-correct lexical position. -/
@[expose] public def lookup
    {f : ι → Type x}
    (position : Var o Γ a)
    (values : Args f Γ) : f a :=
  position.typeCorrect ▸ values.get position.index

@[simp] public theorem lookup_head
    {f : ι → Type x}
    (value : f a)
    (rest : Args f Γ) :
    (head : Var o (a :: Γ) a).lookup (.cons value rest) = value :=
  private_decl% (by rfl)

@[simp] public theorem lookup_ofIndex
    {f : ι → Type x}
    (values : Args f Γ)
    (i : Fin Γ.length) :
    (ofIndex o i).lookup values = values.get i :=
  private_decl% (by rfl)

@[simp] public theorem lookup_weaken
    {f : ι → Type x}
    (position : Var o Γ a)
    (value : f b)
    (rest : Args f Γ) :
    (position.weaken b).lookup (.cons value rest) = position.lookup rest :=
  private_decl% (by
    rcases position with ⟨index, correct⟩
    rfl)

@[simp] public theorem head_index :
    (head : Var o (a :: Γ) a).index.val = 0 :=
  private_decl% (by rfl)

@[simp] public theorem weaken_index (x : Var o Γ a) (b : ι) :
    (x.weaken b).index.val = x.index.val + 1 :=
  private_decl% (by rfl)

@[simp] public theorem weakenMany_index (x : Var o Γ a) (Δ : List ι) :
    (x.weakenMany Δ).index.val = x.index.val + Δ.length := by
  induction Δ with
  | nil => rfl
  | cons b Δ induction =>
      simp only [weakenMany, weaken_index, induction, List.length_cons]
      omega

@[simp] private theorem cast_index
    (same : a = b) (x : Var o Γ a) :
    (same ▸ x).index = x.index := by
  cases same
  rfl

@[simp] public theorem identity_get_index (o : Type v) (Γ : List ι) (i : Fin Γ.length) :
    ((identity o Γ).get i).index = i := by
  simp [identity]

@[ext] public theorem ext (x y : Var o Γ a)
    (same : x.index.val = y.index.val) : x = y :=
  private_decl% (by
    have indices : x.index = y.index := Fin.ext same
    cases x
    cases y
    cases indices
    rfl)

public instance : DecidableEq (Var o Γ a) := fun x y =>
  decidable_of_iff (x.index.val = y.index.val) ⟨ext x y, fun h => congrArg (·.index.val) h⟩

@[elab_as_elim] private def inductionOn
    {P : ∀ {a}, Var o (b :: Γ) a → Sort z}
    (head : P (Var.head : Var o (b :: Γ) b))
    (tail : ∀ {a} (x : Var o Γ a), P (x.weaken b))
    {a} (x : Var o (b :: Γ) a) : P x := by
  generalize h : x.index = i
  induction i using Fin.cases with
  | zero =>
      have type : b = a := by
        simpa only [h, List.get_cons_zero] using x.typeCorrect
      cases type
      rw [show x = (Var.head : Var o (b :: Γ) b) from
        ext _ _ (by simp [h])]
      exact head
  | succ i =>
      have type : Γ.get i = a := by
        simpa only [h, List.get_cons_succ'] using x.typeCorrect
      cases type
      rw [show x = (ofIndex o i).weaken b from ext _ _ (by simp [h])]
      exact tail _

end Var

/-- A total, type-preserving map between typed contexts. -/
public structure Renaming
    (o : Type v) (p : Type w) {ι : Type u} (Γ Δ : List ι) where
  apply : ∀ {a}, Var o Γ a → Var p Δ a

public instance : CoeFun (Renaming o p Γ Δ)
    (fun _ => ∀ {a}, Var o Γ a → Var p Δ a) where
  coe ρ := ρ.apply

namespace Renaming

/-- The identity renaming. -/
@[expose] public def id (o : Type v) (Γ : List ι) : Renaming o o Γ Γ :=
  ⟨fun x => x⟩

/-- Compose renamings in ordinary function-composition order. -/
@[expose] public def comp
    (σ : Renaming p q Δ Ε) (ρ : Renaming o p Γ Δ) : Renaming o q Γ Ε :=
  ⟨fun x => σ (ρ x)⟩

/-- Shift every target variable beneath one new binder. -/
@[expose] public def weaken
    (ρ : Renaming o p Γ Δ) (b : ι) : Renaming o p Γ (b :: Δ) :=
  ⟨fun x => (ρ x).weaken b⟩

/-- Extend a renaming beneath one matching source and target binder. -/
@[expose] public def lift
    (ρ : Renaming o p Γ Δ) (b : ι) :
    Renaming o p (b :: Γ) (b :: Δ) :=
  private_decl% ⟨fun {a} x => by
    rcases x with ⟨i, correct⟩
    induction i using Fin.cases with
    | zero => exact correct ▸ (Var.head : Var p (b :: Δ) b)
    | succ tail =>
        exact (ρ ⟨tail, by
          simpa only [List.get_cons_succ'] using correct⟩).weaken b⟩

/-- Extend a renaming beneath a matching binder telescope. -/
@[expose] public def liftMany
    (ρ : Renaming o p Γ Δ) :
    (bs : List ι) → Renaming o p (bs ++ Γ) (bs ++ Δ)
  | [] => ρ
  | b :: bs => (ρ.liftMany bs).lift b

/-- Embed the left telescope into an appended context without changing positions. -/
@[expose] public def appendLeft (o : Type v) :
    (Γ Δ : List ι) → Renaming o o Γ (Γ ++ Δ)
  | Γ, Δ => ⟨fun {a} x =>
      let i : Fin (Γ ++ Δ).length := ⟨x.index.val, by
        simp only [List.length_append]
        omega⟩
      have atIndex : (Γ ++ Δ).get i = Γ.get x.index := by
        change (Γ ++ Δ)[x.index.val] = Γ[x.index.val]
        exact List.getElem_append_left x.index.isLt
      (atIndex.trans x.typeCorrect) ▸ Var.ofIndex o i⟩

/-- Embed the right telescope beneath the complete left telescope. -/
@[expose] public def appendRight
    (o : Type v) (Γ Δ : List ι) : Renaming o o Δ (Γ ++ Δ) :=
  ⟨fun x => x.weakenMany Γ⟩

@[simp] public theorem id_apply (x : Var o Γ a) : id o Γ x = x :=
  rfl

@[simp] public theorem comp_apply
    (σ : Renaming p q Δ Ε) (ρ : Renaming o p Γ Δ) (x : Var o Γ a) :
    σ.comp ρ x = σ (ρ x) :=
  rfl

@[simp] public theorem weaken_apply
    (ρ : Renaming o p Γ Δ) (b : ι) (x : Var o Γ a) :
    ρ.weaken b x = (ρ x).weaken b :=
  rfl

@[simp] public theorem lift_head (ρ : Renaming o p Γ Δ) (b : ι) :
    ρ.lift b (Var.head : Var o (b :: Γ) b) =
      (Var.head : Var p (b :: Δ) b) := by
  apply Var.ext
  rfl

@[simp] public theorem lift_weaken
    (ρ : Renaming o p Γ Δ) (b : ι) (x : Var o Γ a) :
    ρ.lift b (x.weaken b) = (ρ x).weaken b := by
  apply Var.ext
  rfl

@[simp] public theorem liftMany_nil (ρ : Renaming o p Γ Δ) :
    (ρ.liftMany [] : Renaming o p Γ Δ) = ρ :=
  rfl

@[simp] public theorem liftMany_cons
    (ρ : Renaming o p Γ Δ) (b : ι) (bs : List ι) :
    ρ.liftMany (b :: bs) = (ρ.liftMany bs).lift b :=
  rfl

@[simp] public theorem appendLeft_index
    (x : Var o Γ a) :
    (appendLeft o Γ Δ x).index.val = x.index.val := by
  simp [appendLeft]

@[simp] public theorem appendRight_index
    (x : Var o Δ a) :
    (appendRight o Γ Δ x).index.val = x.index.val + Γ.length := by
  simp [appendRight]

@[simp] public theorem liftMany_weakenMany
    (ρ : Renaming o p Γ Δ) (bs : List ι) (x : Var o Γ a) :
    ρ.liftMany bs (x.weakenMany bs) = (ρ x).weakenMany bs := by
  induction bs with
  | nil => rfl
  | cons b bs induction =>
      simp only [liftMany, Var.weakenMany, lift_weaken, induction]

@[simp] public theorem comp_id (ρ : Renaming o p Γ Δ) :
    (ρ.comp (id o Γ) : Renaming o p Γ Δ) = ρ := by
  cases ρ
  rfl

@[simp] public theorem id_comp (ρ : Renaming o p Γ Δ) :
    ((id p Δ).comp ρ : Renaming o p Γ Δ) = ρ := by
  cases ρ
  rfl

@[simp] public theorem comp_assoc
    (τ : Renaming q r Ε Ζ)
    (σ : Renaming p q Δ Ε)
    (ρ : Renaming o p Γ Δ) :
    ((τ.comp σ).comp ρ : Renaming o r Γ Ζ) = τ.comp (σ.comp ρ) := by
  rfl

@[ext] public theorem ext
    (ρ σ : Renaming o p Γ Δ)
    (same : ∀ {a} (x : Var o Γ a), ρ x = σ x) :
    (ρ : Renaming o p Γ Δ) = σ := by
  cases ρ with
  | mk left =>
      cases σ with
      | mk right =>
          congr
          funext a x
          exact same x

@[simp] public theorem lift_id (b : ι) :
    (id o Γ).lift b = id o (b :: Γ) :=
  private_decl% (by
    apply Renaming.ext
    intro a x
    exact Var.inductionOn (P := fun x => (id o Γ).lift b x = id o (b :: Γ) x)
      (by simp) (fun x => by simp) x)

@[simp] public theorem lift_comp
    (σ : Renaming p q Δ Ε) (ρ : Renaming o p Γ Δ) (b : ι) :
    (σ.comp ρ).lift b = (σ.lift b).comp (ρ.lift b) :=
  private_decl% (by
    apply Renaming.ext
    intro a x
    exact Var.inductionOn
      (P := fun x => (σ.comp ρ).lift b x = (σ.lift b).comp (ρ.lift b) x)
      (by simp) (fun x => by simp) x)

@[simp] public theorem liftMany_id (bs : List ι) :
    ((id o Γ).liftMany bs : Renaming o o (bs ++ Γ) (bs ++ Γ)) =
      id o (bs ++ Γ) := by
  induction bs with
  | nil => rfl
  | cons b bs induction =>
      simp only [liftMany, induction, lift_id]
      rfl

@[simp] public theorem liftMany_comp
    (σ : Renaming p q Δ Ε) (ρ : Renaming o p Γ Δ) (bs : List ι) :
    ((σ.comp ρ).liftMany bs : Renaming o q (bs ++ Γ) (bs ++ Ε)) =
      (σ.liftMany bs).comp (ρ.liftMany bs) := by
  induction bs with
  | nil => rfl
  | cons b bs induction =>
      simp only [liftMany, induction, lift_comp]
      rfl

end Renaming

end Oria.IR.Scope
