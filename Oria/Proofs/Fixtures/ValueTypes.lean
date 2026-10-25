module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.ValueTypes

open Oria Oria.Persistent Oria.Std

@[value_type]
public structure Empty where
  deriving Oria.Object

@[value_type]
public structure Word where
  value : Int32
  deriving Oria.Object

@[value_type]
public structure Triple where
  x : Int32
  y : Int32
  z : Int32
  deriving Oria.Object

@[value_type]
public structure Quad where
  triple : Triple
  last : Word
  erased : Unit
  deriving Oria.Object

public structure Box where
  value : Quad
  link : Option Int32
  deriving Oria.Object

@[mcfunction]
private def make (x : Val Int32) : Prog .pure Triple := do
  return {x := x, y := x + 1, z := x + 2}

@[mcfunction]
private def total {r : Region} (x : Val Triple r) : Prog .pure Int32 := do
  match x with
  | .mk a b c => return a + b * 10 + c * 100

@[mcfunction]
private def bump (x : Val Quad) : Prog .pure Quad := do
  let t ← make.call (x.triple.x + 1)
  let w ← Word.mk (x.last.value + 1)
  return {triple := t, last := w, erased := Val.unit}

@[mcfunction]
private def loop : Val Int32 → Val Triple → Prog .pure Triple :=
  Prog.fix fun recur n x => do
    if n <= 0 then return x
    else
      let rest ← recur (n - 1) x
      return {x := rest.x + 1, y := rest.y + 2, z := rest.z + 3}

@[mcfunction]
private def acceptEmpty (v : Val Empty) : Prog .pure Int32 := do
  match v with
  | .mk => return 1

@[mcfunction]
private def fallible (n : Val Int32) : Prog .failure Triple := do
  if n < 0 then Prog.fail
  else return {x := n, y := n + 1, z := n + 2}

@[mcfunction]
private def optional (v : Val (Option Triple)) : Prog .pure Int32 := do
  match v with
  | .some t => total.call t
  | .none => return -1

@[root]
private def triple : Root Triple := Root.init do
  let x ← make.call 3
  persist x

@[root]
private def empty : Root Empty := Root.init do
  let x ← Empty.mk
  persist x

@[root]
private def cell : Root (Ref Triple) := Root.init do
  let x ← make.call 7
  let x ← persist x
  Ref.new x

@[root]
private def box : Root Box := Root.init do
  let t ← make.call 1
  let w ← Word.mk 4
  let q ← Quad.mk t w Val.unit
  let n ← Oria.Option.some 19
  let b ← Box.mk q n
  persist b

private def objective : Command.Objective := "value_test.oria"
private def grade : Grade := stateGrade.seq ⟨Req.none, Eff.scoreboardWrite⟩

@[mcfunction]
private def arithmetic : Prog (Grade.handled ⟨Req.none, Eff.scoreboardWrite⟩) Unit := do
  let t ← make.call 2
  let w ← Word.mk 5
  let q ← Quad.mk t w Val.unit
  let q ← bump.call q
  let sum ← total.call q.triple
  (Scoreboard.set (.named "#quad") objective (sum + q.last.value * 1000)).ignore
  let x ← loop.call 4 t
  let sum ← total.call x
  (Scoreboard.set (.named "#recursive") objective sum).ignore
  let x ← make.call 9
  (Scoreboard.set (.named "#sparse") objective x.z).ignore
  let e ← Empty.mk
  let n ← acceptEmpty.call e
  (Scoreboard.set (.named "#empty") objective n).ignore

@[mcfunction]
private def recovery : Prog (Grade.handled ⟨Req.none, Eff.scoreboardWrite⟩) Unit := do
  let value ← Prog.attempt (fallible.call 6)
  let n ← optional.call value
  (Scoreboard.set (.named "#success") objective n).ignore
  let value ← Prog.attempt (fallible.call (-1))
  let n ← optional.call value
  (Scoreboard.set (.named "#failure") objective n).ignore

@[mcfunction]
private def snapshot : Prog (Grade.handled (readGrade.seq ⟨Req.none, Eff.scoreboardWrite⟩)) Unit := do
  let t ← triple
  let sum ← total.call t
  (Scoreboard.set (.named "#root") objective sum).ignore
  let c ← cell
  let t ← Ref.get c
  let sum ← total.call t
  (Scoreboard.set (.named "#ref") objective sum).ignore
  let b ← box
  let sum ← total.call b.value.triple
  (Scoreboard.set (.named "#boxed") objective (sum + b.value.last.value * 1000)).ignore
  match b.link with
  | .some n => (Scoreboard.set (.named "#link") objective n).ignore
  | .none => (Scoreboard.set (.named "#link") objective (-1)).ignore

@[mcfunction]
private def update : Prog (Grade.handled grade) Unit := do
  let c ← cell
  let old ← Ref.get c
  let t ← make.call 11
  let t ← persist t
  Ref.set c t
  triple := t
  let sum ← total.call old
  (Scoreboard.set (.named "#old") objective sum).ignore

@[datapack]
public def arithmeticOnly : Datapack.Spec := Datapack.build {ns := "values_pure"} do
  Datapack.entry "arithmetic" arithmetic.ref

@[datapack]
public def specimen : Datapack.Spec := Datapack.build {ns := "values", registerBudget := 128} do
  Datapack.root "values:triple" triple
  Datapack.root "values:empty" empty
  Datapack.root "values:cell" cell
  Datapack.root "values:box" box
  Datapack.entry "arithmetic" arithmetic.ref
  Datapack.entry "snapshot" snapshot.ref
  Datapack.entry "recovery" recovery.ref
  Datapack.entry "update" update.ref
  Datapack.collector "gc"

@[datapack]
public def allStack : Datapack.Spec := Datapack.build {ns := "values_zero", registerBudget := 6} do
  Datapack.root "values_zero:triple" triple
  Datapack.root "values_zero:empty" empty
  Datapack.root "values_zero:cell" cell
  Datapack.root "values_zero:box" box
  Datapack.entry "arithmetic" arithmetic.ref
  Datapack.entry "snapshot" snapshot.ref
  Datapack.entry "recovery" recovery.ref
  Datapack.entry "update" update.ref
  Datapack.collector "gc"

end Oria.Proofs.Fixtures.ValueTypes
