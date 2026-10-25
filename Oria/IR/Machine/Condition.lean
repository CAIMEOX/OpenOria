module

public import Oria.IR.Common.Operator

namespace Oria.IR.Machine

/-- Branch predicates over scalar operands; an ordinary word is true exactly when it is one. -/
public inductive Condition (a : Type) where
  | isTrue : a → Condition a
  | compare {l r : ObjTy} : BinaryOp l r .bool → a → a → Condition a

public def Condition.traverse {M : Type → Type} [Applicative M] {a b : Type}
    (f : a → M b) : Condition a → M (Condition b)
  | .isTrue v => .isTrue <$> f v
  | .compare op l r => .compare op <$> f l <*> f r

public def Condition.map {a b : Type} (f : a → b) (c : Condition a) : Condition b :=
  Id.run (c.traverse (pure ∘ f))

@[expose] public def Condition.test {l r : ObjTy} : BinaryOp l r .bool → Int32 → Int32 → Bool
  | .le, l, r => l ≤ r
  | .lt, l, r => l < r
  | .eq, l, r | .beq, l, r => l == r

@[expose] public def Condition.eval {a : Type} (value : a → Int32) : Condition a → Bool
  | .isTrue v => value v == 1
  | .compare op l r => test op (value l) (value r)

public theorem Condition.eval_map {a b : Type} (f : a → b) (value : b → Int32) (c : Condition a) :
    (c.map f).eval value = c.eval (value ∘ f) := by
  cases c <;> rfl

public theorem Condition.materialized {a b : ObjTy} (op : BinaryOp a b .bool) (l r : Int32) :
    ((if test op l r then (1 : Int32) else 0) == 1) = test op l r := by
  cases h : test op l r <;> rfl

end Oria.IR.Machine
