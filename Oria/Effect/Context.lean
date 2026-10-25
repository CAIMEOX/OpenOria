module

public import Oria.Effect.Grade

namespace Oria

/-- A pure transformation of the execution requirements around a scoped command.

`need` is read from the incoming context and `give` is available to the body
after the transformation.  Requirement rows are finite bit sets, so a
transformation can be composed without introducing a second effect grade.
-/
public structure ContextChange where
  need : ReqRow
  give : ReqRow
  deriving BEq, DecidableEq, Repr

namespace ContextChange

@[expose] public def id : ContextChange :=
  ⟨0#8, 0#8⟩

@[expose] public def apply (c : ContextChange) (q : ReqRow) : ReqRow :=
  c.need ||| (q &&& ~~~c.give)

@[expose] public def seq (a b : ContextChange) : ContextChange :=
  ⟨a.need ||| (b.need &&& ~~~a.give), a.give ||| b.give⟩

private theorem bool_apply_id (q : Bool) :
    (false || (q && !false)) = q := by
  cases q <;> decide

private theorem bool_apply_seq (an ag bn bg q : Bool) :
    ((an || (bn && !ag)) || (q && !(ag || bg))) =
      (an || ((bn || (q && !bg)) && !ag)) := by
  cases an <;> cases ag <;> cases bn <;> cases bg <;> cases q <;> decide

private theorem bool_seq_assoc (an ag bn bg cn : Bool) :
    ((an || (bn && !ag)) || (cn && !(ag || bg))) =
      (an || ((bn || (cn && !bg)) && !ag)) := by
  cases an <;> cases ag <;> cases bn <;> cases bg <;> cases cn <;>
    decide

private theorem bool_apply_mono (n g x y : Bool) (h : (x || y) = y) :
    ((n || (x && !g)) || (n || (y && !g))) = (n || (y && !g)) := by
  cases n <;> cases g <;> cases x <;> cases y <;> simp_all

private theorem bool_available_iff (n q available g : Bool) :
    ((n || (q && !g)) || available) = available ↔
      ((n || available) = available) ∧
        ((q || (available || g)) = (available || g)) := by
  cases n <;> cases q <;> cases available <;> cases g <;> decide

@[simp] public theorem apply_id (q : ReqRow) : apply id q = q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
  simp only [apply, id, BitVec.getLsbD_zero, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not]
  simpa only [hi', Bool.true_and] using
    bool_apply_id (q.getLsbD i)

public theorem apply_seq (a b : ContextChange) (q : ReqRow) :
    apply (seq a b) q = apply a (apply b q) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
  simp only [apply, seq, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not]
  simpa only [hi', Bool.true_and] using
    bool_apply_seq (a.need.getLsbD i) (a.give.getLsbD i)
      (b.need.getLsbD i) (b.give.getLsbD i) (q.getLsbD i)

public theorem seq_assoc (a b c : ContextChange) :
    seq (seq a b) c = seq a (seq b c) := by
  rcases a with ⟨an, ag⟩
  rcases b with ⟨bn, bg⟩
  rcases c with ⟨cn, cg⟩
  simp only [seq, ContextChange.mk.injEq]
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not]
    simpa only [hi', Bool.true_and] using
      bool_seq_assoc (an.getLsbD i) (ag.getLsbD i)
        (bn.getLsbD i) (bg.getLsbD i) (cn.getLsbD i)
  · exact BitVec.or_assoc _ _ _

@[simp] public theorem id_seq (c : ContextChange) : seq id c = c := by
  cases c
  simp only [id, seq, BitVec.not_zero,
    BitVec.and_allOnes, BitVec.zero_or]

@[simp] public theorem seq_id (c : ContextChange) : seq c id = c := by
  cases c
  simp only [id, seq, BitVec.zero_and,
    BitVec.or_zero]

/-- `apply` is monotone in the incoming requirement set. -/
public theorem apply_mono (c : ContextChange) {x y : ReqRow}
    (h : x ||| y = y) : apply c x ||| apply c y = apply c y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
  have hxy := BitVec.eq_of_getLsbD_eq_iff.mp h i hi
  simp only [BitVec.getLsbD_or] at hxy
  simp only [apply, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not]
  simpa only [hi', Bool.true_and] using
    bool_apply_mono (c.need.getLsbD i) (c.give.getLsbD i)
      (x.getLsbD i) (y.getLsbD i) hxy

/-- A scoped computation is admissible exactly when its own needs are available
and the body's needs are available after the supplied context is installed. -/
public theorem apply_available_iff (c : ContextChange) (q available : ReqRow) :
    apply c q ||| available = available ↔
      c.need ||| available = available ∧
        q ||| (available ||| c.give) = available ||| c.give := by
  constructor
  · intro h
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
      have h' := BitVec.eq_of_getLsbD_eq_iff.mp h i hi
      simp only [apply, BitVec.getLsbD_or, BitVec.getLsbD_and,
        BitVec.getLsbD_not] at h'
      have h' := (bool_available_iff (c.need.getLsbD i)
        (q.getLsbD i) (available.getLsbD i) (c.give.getLsbD i)).mp
        (by simpa only [hi', Bool.true_and] using h')
      simpa only [BitVec.getLsbD_or] using h'.1
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
      have h' := BitVec.eq_of_getLsbD_eq_iff.mp h i hi
      simp only [apply, BitVec.getLsbD_or, BitVec.getLsbD_and,
        BitVec.getLsbD_not] at h'
      have h' := (bool_available_iff (c.need.getLsbD i)
        (q.getLsbD i) (available.getLsbD i) (c.give.getLsbD i)).mp
        (by simpa only [hi', Bool.true_and] using h')
      simpa only [BitVec.getLsbD_or] using h'.2
  · rintro ⟨hneed, hbody⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi' : decide (i < 8) = true := of_decide_eq_true (by simp [hi])
    have hneed' := BitVec.eq_of_getLsbD_eq_iff.mp hneed i hi
    have hbody' := BitVec.eq_of_getLsbD_eq_iff.mp hbody i hi
    have hneed' : (c.need.getLsbD i || available.getLsbD i) = available.getLsbD i := by
      simpa only [BitVec.getLsbD_or] using hneed'
    have hbody' : (q.getLsbD i || (available.getLsbD i || c.give.getLsbD i)) =
        (available.getLsbD i || c.give.getLsbD i) := by
      simpa only [BitVec.getLsbD_or] using hbody'
    have h' := (bool_available_iff (c.need.getLsbD i)
      (q.getLsbD i) (available.getLsbD i) (c.give.getLsbD i)).mpr
      ⟨hneed', hbody'⟩
    simpa only [apply, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, hi', Bool.true_and] using h'

end ContextChange

end Oria
