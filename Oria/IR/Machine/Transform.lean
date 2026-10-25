module

public import Oria.IR.Machine.Definition

namespace Oria.IR.Machine

/-- Simultaneous scalar substitution, lifted beneath each instruction's result tuple. -/
public abbrev Subst (n m : Nat) := Fin n → Atom m

@[expose] public def Atom.subst {n m : Nat} (σ : Subst n m) : Atom n → Atom m
  | .var i => σ i
  | .lit v => .lit v

@[expose] public def Subst.lift {n m : Nat} (σ : Subst n m) (k : Nat) : Subst (k + n) (k + m) :=
  fun i => if h : i.val < k then .var ⟨i.val, by omega⟩
    else (σ ⟨i.val - k, by omega⟩).weaken k

@[simp] public theorem Atom.subst_id {n : Nat} (v : Atom n) : v.subst Atom.var = v := by
  cases v <;> rfl

@[simp] public theorem Subst.lift_new {n m k : Nat} (σ : Subst n m) (i : Fin k) :
    σ.lift k ⟨i.val, by omega⟩ = .var ⟨i.val, by omega⟩ := by
  simp [Subst.lift, i.isLt]

@[simp] public theorem Subst.lift_old {n m : Nat} (σ : Subst n m) (k : Nat) (i : Fin n) :
    σ.lift k ⟨k + i.val, by omega⟩ = (σ i).weaken k := by
  have h : ¬ k + i.val < k := by omega
  simp [Subst.lift, h]

/-- Map operands while retaining operation order, callees and physical layouts. -/
public def Op.map {f : List Signature} {n m r : Nat} (a : Atom n → Atom m) :
    Op f n r → Op f m r
  | .division l r => .division (a l) (a r)
  | .nbt op values => .nbt op (values.map a)
  | .checkpoint forced => .checkpoint forced
  | .unary op v => .unary op (a v)
  | .binary op l r => .binary op (a l) (a r)
  | .allocate layout vs => .allocate layout (vs.map a)
  | .tag v => .tag (a v)
  | .project layout v => .project layout (a v)
  | .promote ty v => .promote ty (a v)
  | .rootGet root => .rootGet root
  | .rootSet root vs => .rootSet root (vs.map a)
  | .refNew layout vs => .refNew layout (vs.map a)
  | .refGet layout v => .refGet layout (a v)
  | .refSet layout v vs => .refSet layout (a v) (vs.map a)
  | .command request => .command (request.map a)
  | .call ref vs => .call ref (vs.map a)
  | .execute scope canFail ref vs => .execute (scope.map a) canFail ref (vs.map a)

public def Edge.subst {l : List Nat} {n m : Nat} (σ : Subst n m) (e : Edge l n) : Edge l m :=
  ⟨e.target, e.values.map (Atom.subst σ)⟩

/-- Substitute operands and rewrite whole edges, including their target parameter tuples. -/
public def Terminator.traverse {M : Type → Type} [Monad M] {l k : List Nat} {r n m : Nat}
    (σ : Subst n m) (next : Edge l m → M (Edge k m)) :
    Terminator l r n → M (Terminator k r m)
  | .ret vs => pure (.ret (vs.map (Atom.subst σ)))
  | .jump e => .jump <$> edge e
  | .branch c yes no => .branch (c.map (Atom.subst σ)) <$> edge yes <*> edge no
  | .switch v cases fallback =>
      .switch (v.subst σ) <$> cases.mapM (fun (tag, e) => (tag, ·) <$> edge e) <*>
        fallback.mapM edge
where
  edge (e : Edge l n) : M (Edge k m) := next (e.subst σ)

/-- Rewrite a terminator after substituting the complete instruction prefix. -/
public def Body.rewrite {M : Type → Type} [Monad M] {f : List Signature} {l k : List Nat}
    {r n m : Nat} (σ : Subst n m)
    (finish : {n : Nat} → Terminator l r n → M (Body f k r n)) :
    Body f l r n → M (Body f k r m)
  | .done exit => finish (Id.run (exit.traverse σ pure))
  | .step (m := a) op next => .step (op.map (Atom.subst σ)) <$> next.rewrite (σ.lift a) finish

public def Body.subst {f : List Signature} {l : List Nat} {r n m : Nat}
    (σ : Subst n m) (body : Body f l r n) : Body f l r m :=
  Id.run (body.rewrite σ (fun exit => pure (.done exit)))

public def Body.exit {f : List Signature} {l : List Nat} {r n : Nat} :
    Body f l r n → (m : Nat) × Terminator l r m
  | .done exit => ⟨_, exit⟩
  | .step _ next => next.exit

/-- Fold instruction metadata without exposing or rebuilding the scoped prefix. -/
public def Body.foldOps {α : Type} {f : List Signature} {l : List Nat} {r n : Nat}
    (visit : {n m : Nat} → α → Op f n m → α) (initial : α) : Body f l r n → α
  | .done _ => initial
  | .step op next => next.foldOps visit (visit initial op)

end Oria.IR.Machine
