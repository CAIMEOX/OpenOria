module

public import Init.Data.SInt
public import Init.Data.List.Lemmas

namespace Oria.Lower.DP121.Transfer

universe u v w

public inductive Source (l : Type) where
  | loc : l → Source l
  | imm : Int32 → Source l
  deriving BEq, DecidableEq, Repr

public structure Move (l : Type) where
  target : l
  source : Source l
  deriving BEq, DecidableEq, Repr

namespace Source

@[expose] public def read {a : Sort u} {l : Type}
    (literal : Int32 → a) (state : l → a) : Source l → a
  | .loc x => state x
  | .imm n => literal n

end Source

private def write {l : Sort u} {a : Sort v} [DecidableEq l]
    (state : l → a) (target : l) (value : a) : l → a :=
  fun x => if x = target then value else state x

-- A data-valued fold step captures the read before publishing the next store closure.
@[noinline] private def eagerStep {l : Type} {a : Type u} [DecidableEq l]
    (literal : Int32 → a) (state : ULift.{0} (l → a)) (move : Move l) : ULift.{0} (l → a) :=
  ⟨write state.down move.target (move.source.read literal state.down)⟩

private def execute {l : Type} {a : Type u} [DecidableEq l] (literal : Int32 → a)
    (initial : l → a) (code : List (Move l)) : l → a :=
  (code.foldl (eagerStep literal) ⟨initial⟩).down

private theorem execute_eq_fold {l : Type} {a : Type u} [DecidableEq l]
    (literal : Int32 → a) (initial : l → a) (code : List (Move l)) :
    execute literal initial code =
      code.foldl (fun state move => write state move.target (move.source.read literal state)) initial := by
  unfold execute
  symm
  apply List.foldl_hom (fun state : ULift.{0} (l → a) => state.down)
  intro state move
  rfl

private def parallel {l : Type} {a : Type u} [DecidableEq l] (literal : Int32 → a)
    (initial : l → a) (moves : List (Move l)) : l → a :=
  moves.foldl (fun state move => write state move.target (move.source.read literal initial)) initial

public def run {l : Type} [DecidableEq l]
    (state : l → Int32) (code : List (Move l)) : l → Int32 :=
  execute id state code

public def simultaneous {l : Type} [DecidableEq l]
    (state : l → Int32) (moves : List (Move l)) : l → Int32 :=
  parallel id state moves

private theorem read_map {a : Sort u} {b : Sort v} {l : Type} (f : a → b) (literal : Int32 → a)
    (state : l → a) (source : Source l) :
    source.read (f ∘ literal) (f ∘ state) = f (source.read literal state) := by
  cases source <;> rfl

private theorem write_map {l : Sort u} {a : Sort v} {b : Sort w} [DecidableEq l] (f : a → b)
    (state : l → a) (target : l) (value : a) :
    write (f ∘ state) target (f value) = f ∘ write state target value := by
  funext x
  simp only [write, Function.comp_apply]
  split <;> rfl

private theorem execute_map {l : Type} {a : Type u} {b : Type v} [DecidableEq l] (f : a → b)
    (literal : Int32 → a) (initial : l → a) (code : List (Move l)) :
    execute (f ∘ literal) (f ∘ initial) code = f ∘ execute literal initial code := by
  rw [execute_eq_fold, execute_eq_fold]
  apply List.foldl_hom (fun state => f ∘ state)
  intro state move
  rw [read_map, write_map]

private theorem parallel_map {l : Type} {a : Type u} {b : Type v} [DecidableEq l] (f : a → b)
    (literal : Int32 → a) (initial : l → a) (moves : List (Move l)) :
    parallel (f ∘ literal) (f ∘ initial) moves = f ∘ parallel literal initial moves := by
  unfold parallel
  apply List.foldl_hom (fun state => f ∘ state)
  intro state move
  rw [read_map, write_map]

private theorem fold_untouched {l : Type} {a : Type u} [DecidableEq l]
    (value : (l → a) → Source l → a) (initial : l → a)
    (code : List (Move l)) (x : l) (h : x ∉ code.map Move.target) :
    (code.foldl (fun state move => write state move.target (value state move.source)) initial) x =
      initial x := by
  induction code generalizing initial with
  | nil => rfl
  | cons move rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp only [List.foldl_cons]
      rw [ih _ h.2]
      simp [write, h.1]

/-- A schedule certificate concerns every input store. -/
public structure Sequence {l : Type} [DecidableEq l] (temporary : l) (moves : List (Move l)) where
  code : List (Move l)
  correct : ∀ state x, x ≠ temporary → run state code x = simultaneous state moves x

private def checked {l : Type} [DecidableEq l] (temporary : l)
    (moves code : List (Move l)) : Option (Sequence temporary moves) := do
  let actual := execute Source.imm Source.loc code
  let expected := parallel Source.imm Source.loc moves
  let observed := moves.map Move.target ++ code.map Move.target
  if h : observed.all (fun x => decide (x = temporary ∨ actual x = expected x)) then
    have symbolic : ∀ x, x ≠ temporary → actual x = expected x := by
      intro x outside
      by_cases membership : x ∈ observed
      · have observedEq := List.all_eq_true.mp h x membership
        exact (of_decide_eq_true observedEq).resolve_left outside
      · have absent : x ∉ moves.map Move.target ∧ x ∉ code.map Move.target := by
          simpa only [observed, List.mem_append, not_or] using membership
        have a := fold_untouched (fun state source => source.read Source.imm state)
          Source.loc code x absent.2
        have b := fold_untouched (fun _ source => source.read Source.imm Source.loc)
          Source.loc moves x absent.1
        exact (congrFun (execute_eq_fold Source.imm Source.loc code) x).trans (a.trans b.symm)
    pure ⟨code, by
      intro state x outside
      let f := Source.read id state
      have actualMap := congrFun (execute_map f Source.imm Source.loc code) x
      have expectedMap := congrFun (parallel_map f Source.imm Source.loc moves) x
      have literals : f ∘ Source.imm = id := rfl
      have locations : f ∘ Source.loc = state := rfl
      rw [literals, locations] at actualMap expectedMap
      exact actualMap.trans ((congrArg f (symbolic x outside)).trans expectedMap.symm)⟩
  else none

private def sourceLocation {l : Type} : Source l → Option l
  | .loc x => some x
  | .imm _ => none

private def resolve {l : Type} [DecidableEq l] (temporary : l) :
    Nat → List (Move l) → List (Move l) → Option (List (Move l))
  | 0, [], code => some code.reverse
  | 0, _ :: _, _ => none
  | _ + 1, [], code => some code.reverse
  | fuel + 1, moves, code =>
      let sources := moves.filterMap (sourceLocation ∘ Move.source)
      match moves.find? (fun move => decide (move.target ∉ sources)) with
      | some move => resolve temporary fuel (moves.erase move) (move :: code)
      | none =>
          match moves with
          | [] => some code.reverse
          | move :: _ =>
              let moves := moves.map fun item =>
                { item with source := match item.source with
                  | .loc x => if x = move.target then .loc temporary else .loc x
                  | .imm n => .imm n }
              resolve temporary fuel moves (⟨temporary, .loc move.target⟩ :: code)

/-- Sequentialize with one temporary and validate the resulting symbolic values. -/
public def schedule {l : Type} [DecidableEq l]
    (temporary : l) (moves : List (Move l)) : Option (Sequence temporary moves) := do
  unless (moves.map Move.target).Nodup do failure
  unless moves.all (fun move => decide
      (move.target ≠ temporary ∧ move.source ≠ .loc temporary)) do failure
  let active := moves.filter fun move => decide (move.source ≠ .loc move.target)
  let code ← resolve temporary (2 * active.length + 1) active []
  checked temporary moves code

end Oria.Lower.DP121.Transfer
