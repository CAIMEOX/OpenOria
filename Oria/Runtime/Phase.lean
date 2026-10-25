module

namespace Oria.Runtime

/-- Exclusive use of a datapack's registers and invocation workspace. -/
public inductive Phase where
  | idle | entry | task | collect | initialize
  deriving DecidableEq, Repr

@[expose] public def Phase.code : Phase → Int32
  | .idle => 0 | .entry => 1 | .task => 2 | .collect => 3 | .initialize => 4

public theorem Phase.active_code (p : Phase) : 1 ≤ p.code ↔ p ≠ .idle := by
  cases p <;> decide

/-- A parked task owns a separate arena, retained until completion or cancellation. -/
public structure State where
  phase : Phase
  taskLive : Bool
  deriving DecidableEq

/-- Collection requires quiescence of both ordinary execution and parked tasks. -/
@[expose] public def State.CanEnter (s : State) (next : Phase) : Prop :=
  s.phase = .idle ∧ next ≠ .idle ∧ (next = .collect → s.taskLive = false)

public theorem State.enter_requires_idle {s : State} {next : Phase}
    (h : s.CanEnter next) : s.phase = .idle := h.1

public theorem State.collection_requires_quiescence {s : State}
    (h : s.CanEnter .collect) : s.phase = .idle ∧ s.taskLive = false :=
  ⟨h.1, h.2.2 rfl⟩

public theorem State.active_excludes_entry {s : State} {next : Phase}
    (active : s.phase ≠ .idle) : ¬s.CanEnter next :=
  fun h => active h.1

end Oria.Runtime
