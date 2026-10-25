module

import Init.Data.BitVec.Lemmas

namespace Oria

/-- Requirements supplied by the eventual execution context. -/
public abbrev ReqRow := BitVec 8

/-- Observable object-program effects. Physical compiler effects do not belong here. -/
public abbrev EffRow := BitVec 16

public structure Grade where
  req : ReqRow
  eff : EffRow
  deriving BEq, DecidableEq, Hashable, Repr

namespace Grade

private theorem or_join_right {w : Nat} (a b k : BitVec w) :
    (a ||| b) ||| k = (a ||| k) ||| (b ||| k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases k.getLsbD i <;> decide

@[expose] public def pure : Grade :=
  { req := 0#8, eff := 0#16 }

/-- A recoverable exit with no payload. -/
@[expose] public def failure : Grade := ⟨0#8, 2048#16⟩

/-- Cooperative suspension at a compiler-recognized task boundary. -/
@[expose] public def suspension : Grade := ⟨0#8, 4096#16⟩

@[expose] public def canSuspend (g : Grade) : Bool := g.eff.getLsbD 12

/-- Whether a computation may leave through its recoverable failure exit. -/
@[expose] public def canFail (g : Grade) : Bool := g.eff.getLsbD 11

/-- Mask the failure exit while preserving context requirements and storage effects. -/
@[expose] public def handled (g : Grade) : Grade :=
  { g with eff := g.eff &&& ~~~failure.eff }

@[expose] public def seq (a b : Grade) : Grade :=
  { req := a.req ||| b.req, eff := a.eff ||| b.eff }

@[expose] public def join (a b : Grade) : Grade :=
  { req := a.req ||| b.req, eff := a.eff ||| b.eff }

/-- The actual requirements and effects are contained in a declared upper bound. -/
@[expose] public def Below (actual declared : Grade) : Prop :=
  actual.req ||| declared.req = declared.req ∧
    actual.eff ||| declared.eff = declared.eff

public instance (a b : Grade) : Decidable (a.Below b) :=
  inferInstanceAs (Decidable
    (a.req ||| b.req = b.req ∧ a.eff ||| b.eff = b.eff))

/-- Join a statically known, possibly heterogeneous list of branch grades. -/
@[expose] public def joins : List Grade → Grade
  | [] => pure
  | [grade] => grade
  | grade :: rest => grade.join (joins rest)

@[simp] public theorem joins_singleton (grade : Grade) : joins [grade] = grade := rfl

@[simp] public theorem joins_pair (left right : Grade) :
    joins [left, right] = left.join right := rfl

public theorem seq_assoc (a b c : Grade) :
    (a.seq b).seq c = a.seq (b.seq c) := by
  cases a
  cases b
  cases c
  simp [seq, BitVec.or_assoc]

@[simp↓] public theorem handled_seq (g h : Grade) :
    (g.seq h).handled = g.handled.seq h.handled := by
  cases g; cases h
  simp [handled, seq, BitVec.and_or_distrib_right]

@[simp] public theorem handled_pure : pure.handled = pure := by decide

@[simp] public theorem handled_failure : failure.handled = pure := by decide

@[simp] public theorem handled_idem (g : Grade) : g.handled.handled = g.handled := by
  cases g
  simp [handled, BitVec.and_assoc]

/-- Catching cannot introduce a failure exit when its recovery has none. -/
@[simp] public theorem handled_cannot_fail (g : Grade) : g.handled.canFail = false := by
  simp [handled, canFail, failure]

@[simp] public theorem pure_seq (g : Grade) : pure.seq g = g := by
  cases g
  simp [pure, seq]

@[simp] public theorem seq_pure (g : Grade) : g.seq pure = g := by
  cases g
  simp [pure, seq]

public theorem join_assoc (a b c : Grade) :
    (a.join b).join c = a.join (b.join c) := by
  cases a
  cases b
  cases c
  simp [join, BitVec.or_assoc]

public theorem join_comm (a b : Grade) : a.join b = b.join a := by
  cases a
  cases b
  simp [join, BitVec.or_comm]

@[simp] public theorem join_idem (g : Grade) : g.join g = g := by
  cases g
  simp [join]

@[simp] public theorem seq_idem (g : Grade) : g.seq g = g :=
  join_idem g

@[simp] public theorem pure_join (g : Grade) : pure.join g = g := by
  cases g
  simp [pure, join]

@[simp] public theorem below_refl (g : Grade) : Below g g := by
  cases g
  simp [Below]

@[simp] public theorem pure_below (g : Grade) : Below pure g := by
  cases g
  simp [Below, pure]

public theorem below_join_left (g h : Grade) : g.Below (g.join h) := by
  cases g
  cases h
  simp [Below, join, ← BitVec.or_assoc]

public theorem below_join_right (g h : Grade) : h.Below (g.join h) := by
  simpa only [join_comm h g] using below_join_left h g

public theorem seq_join_right (a b k : Grade) :
    (a.join b).seq k = (a.seq k).join (b.seq k) := by
  cases a
  cases b
  cases k
  simp only [seq, join, Grade.mk.injEq]
  exact ⟨or_join_right _ _ _, or_join_right _ _ _⟩

end Grade

end Oria
