module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

/-!
# Round ledger

This example records wins and losses across invocations. Its public entries also exercise
immutable records and graded computation inference. The native language acceptance suite
runs the same program with scoreboard registers and with stack-resident locals.
-/

namespace Oria.Examples.RoundLedger

open Oria.Std Oria.Datapack Oria.Persistent

/-- A player's cumulative round statistics. -/
public structure Stats where
  /-- Completed wins. -/
  wins : Int32
  /-- Completed losses. -/
  losses : Int32
  /-- Completed rounds, including draws. -/
  rounds : Int32
  deriving Oria.Object

private def scores : Command.Objective := "ledger.points"
private def input : Std.Command.Arg.ScoreHolder := .named "#input"
/-- The effect bound for ordered score-reading and score-writing programs. -/
@[expose] public def readWrite : Grade := ⟨Req.none, Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure⟩

@[root]
private def saved : Root Stats := Root.init do
  let s : Val Stats ← .mk 0 0 0
  persist s

@[mcfunction]
private def setup := (Scoreboard.Objectives.add scores .dummy).ignore

@[mcfunction]
private def tally {r : Region} (s : Val Stats r) : Prog .pure Int32 := do
  return s.wins * 100 + s.losses * 10 + s.rounds

@[mcfunction]
private def won {r : Region} (s : Val Stats r) : Prog .pure Stats := do
  return { s with wins := s.wins + 1, rounds := s.rounds + 1 }

@[mcfunction]
private def advance (s : Val Stats) (code : Val Int32) : Prog .pure Stats := do
  match s, code with
  | .mk w l n, 1 => return .mk (w + 1) l (n + 1)
  | .mk w l n, 2 => return .mk w (l + 1) (n + 1)
  | .mk w l n, _ => return .mk w l (n + 1)

private def report (result : Val (Option Int32)) := show Prog _ Unit from do
  match result with
  | .none =>
    (Scoreboard.set (.named "#status") scores (.static 0)).ignore
    (Scoreboard.set (.named "#result") scores (.static (-999))).ignore
  | .some n =>
    (Scoreboard.set (.named "#status") scores (.static 1)).ignore
    (Scoreboard.set (.named "#result") scores (.dynamic n)).ignore

private def capture {g : Grade} (action : Prog g Int32) := show Prog _ Unit from do
  let result : Val (Option Int32) ← Prog.attempt <| action
  report result

@[mcfunction]
private def decode (n : Val Int32) : Prog .failure Int32 := do
  match n with
  | 0 => return n
  | 1 => return n
  | 2 => return n
  | _ => Prog.fail

@[mcfunction]
private def play := show Prog _ Int32 from do
  let n ← Scoreboard.get input scores
  let n ← decode.call n
  let old ← saved
  let next ← advance.call old n
  let durable ← persist next
  saved := durable
  let total ← tally.call next
  let visits ← Scoreboard.get (.named "#visits") scores
  Scoreboard.set (.named "#visits") scores (.dynamic (visits + 1))
  return total

/-- Consume one checked round input and report success or failure. Successful rounds commit
an explicitly promoted record; an absent or invalid input leaves the ledger unchanged. -/
@[mcfunction]
public def round := capture play.call

/-- Observe the durable root through a region-polymorphic named function. -/
@[mcfunction]
public def snapshot := show Prog _ Unit from do
  let s ← saved
  let n ← tally.call s
  (Scoreboard.set (.named "#total") scores (.dynamic n)).ignore

/-- Replace the root with an explicitly promoted zero record. -/
@[mcfunction]
public def reset := show Prog _ Unit from do
  let s : Val Stats ← .mk 0 0 0
  let s ← persist s
  saved := s

/-- Construct a new record while retaining the original across named calls. -/
@[mcfunction]
public def records := show Prog _ Unit from do
  let s : Val Stats ← { wins := 2, losses := 3, rounds := 5 }
  let next ← won.call s
  let before ← tally.call s
  let after ← tally.call next
  (Scoreboard.set (.named "#old") scores (.dynamic before)).ignore
  (Scoreboard.set (.named "#new") scores (.dynamic after)).ignore

/-- Keep a persistent snapshot alive while replacing the root with a new record. -/
@[mcfunction]
public def durableRecords := show Prog _ Unit from do
  let s ← saved
  let next ← won.call s
  let durable ← persist next
  saved := durable
  let before ← tally.call s
  let after ← tally.call durable
  (Scoreboard.set (.named "#old") scores (.dynamic before)).ignore
  (Scoreboard.set (.named "#new") scores (.dynamic after)).ignore

@[mcfunction]
private def append (digit : Val Int32) : Prog readWrite Unit := do
  let previous ← Scoreboard.get (.named "#trace") scores
  let next := previous * 10 + digit
  Scoreboard.set (.named "#trace") scores (.dynamic next)
  return Val.unit

@[mcfunction]
private def guarded (n : Val Int32) : Prog readWrite Int32 := do
  append.call 1
  if n < 0 then
    return -10
  if n == 99 then
    let _ ← Scoreboard.get (.named "#unavailable") scores
    Prog.pure Val.unit
  if n == 0 then
    append.call 2
  else
    append.call 3
  append.call 4
  return n + 7

/-- A guarded result with one shared continuation after a dynamic branch.
The trace is 1 on the negative path, 124 on zero, and 134 on positive input. -/
@[mcfunction]
public def control := capture (show Prog _ Int32 from do
  let n ← Scoreboard.get input scores
  guarded.call n)

@[mcfunction]
private def selected (n : Val Int32) : Prog readWrite Int32 := do
  append.call 1
  match n with
  | -1 => return -11
  | 0 => append.call 2
  | 1 => append.call 3
  | _ => append.call 4
  append.call 5
  return n

/-- Multi-arm integer matching followed by one shared suffix. -/
@[mcfunction]
public def selection := capture (show Prog _ Int32 from do
  let n ← Scoreboard.get input scores
  selected.call n)

/-- Inspect a captured result, recover a local value, and continue with ordered effects.
A successful zero remains zero; the failure fallback is -7. -/
@[mcfunction]
public def recovery := capture (show Prog _ Int32 from do
  let n ← Prog.getD (Scoreboard.get input scores) (-7)
  append.call 9
  return n)

/-- Map a score once, preserving command failure. -/
@[mcfunction]
public def mapped := show Prog _ Unit from do
  capture <| Prog.map (fun n => n * 2 + 1) (Scoreboard.get input scores)

/-- Execute a dependent fallible continuation after a successful read. -/
@[mcfunction]
public def bound := show Prog _ Unit from do
  capture <| Prog.bind (Scoreboard.get input scores) fun n =>
    show Prog readWrite Int32 from do
      append.call 5
      return n + 10

/-- Run the ordinary fallback only when the read fails. -/
@[mcfunction]
public def recovered := capture (show Prog _ Int32 from do
  let n ← Prog.orElse (Scoreboard.get input scores) (show Prog readWrite.handled Int32 from do
    append.call 8 |>.ignore
    return 44)
  return n)

/-- Retry a failed read with a fallible fallback. -/
@[mcfunction]
public def retried := show Prog _ Unit from do
  capture <| Prog.orElse (Scoreboard.get input scores)
    (show Prog readWrite Int32 from do
      append.call 7
      let n ← Scoreboard.get (.named "#fallback") scores
      return n)

/-- Observe the success flag while leaving the native payload unused. -/
@[mcfunction]
public def tested := capture (show Prog _ Int32 from do
  let ok ← Prog.isSuccess (Scoreboard.get input scores)
  if ok then return 1 else return 0)

/-- Discard a failed read and retain the following effect and successful result. -/
@[mcfunction]
public def ignored := capture (show Prog _ Int32 from do
  (Scoreboard.get (.named "#unavailable") scores).ignore
  append.call 7
  return 0)

/-- A return from an inner object block resumes the enclosing block's continuation. -/
@[mcfunction]
public def nested := capture (show Prog _ Int32 from do
  let n ← Scoreboard.get input scores
  let x ← (show Prog readWrite Int32 from do
    if n < 0 then return -2
    append.call 2
    return n + 2)
  append.call 6
  return x)

private def generate (digits : List Int32) : Prog readWrite Int32 :=
  do
    for digit in digits do
      append.call (I32.lit digit)
    return 0

/-- A finite host list generates three ordered object-level calls. -/
@[mcfunction]
public def batch := capture (generate [2, 3, 4])

/-- The empty host list retains its successful zero and emits no score update. -/
@[mcfunction]
public def emptyBatch := capture (generate [])

/-- Host iteration supports local continue and break; the shared outer suffix remains live. -/
@[mcfunction]
public def loopControl := capture (show Prog _ Int32 from do
  let limit ← Scoreboard.get input scores
  for digit in ([1, 2, 3, 4] : List Int32) do
    if digit == 2 then continue
    if limit == I32.lit digit then break
    append.call (I32.lit digit)
  append.call 9
  return limit)

/-- Return from an iteration exits its enclosing object block. -/
@[mcfunction]
public def loopReturn := capture (show Prog _ Int32 from do
  let limit ← Scoreboard.get input scores
  for digit in ([1, 2, 3, 4] : List Int32) do
    if limit == I32.lit digit then return I32.lit (digit + 10)
    append.call (I32.lit digit)
  append.call 9
  return 0)

/-- Arrays and bounded host ranges retain source order. -/
@[mcfunction]
public def collections := capture (show Prog _ Int32 from do
  for digit in (#[(1 : Int32), 2]) do
    append.call (I32.lit digit)
  for digit in ((3 : Nat)...5) do
    append.call (I32.lit (Int32.ofNat digit))
  return 0)

/-- Loop statements propagate command failure and discard the successful native payload. -/
@[mcfunction]
public def nativeLoop := capture (show Prog _ Int32 from do
  for digit in ([1, 2, 3] : List Int32) do
    Scoreboard.set (.named "#native") scores (.static digit)
  return 7)

private def entries : Builder Unit := do
  onLoad setup.ref
  entry "records" records.ref
  entry "durable-records" durableRecords.ref
  entry "round" round.ref
  entry "snapshot" snapshot.ref
  entry "reset" reset.ref
  entry "control" control.ref
  entry "selection" selection.ref
  entry "recovery" recovery.ref
  entry "ignored" ignored.ref
  entry "batch" batch.ref
  entry "empty-batch" emptyBatch.ref
  entry "nested" nested.ref
  entry "loop-control" loopControl.ref
  entry "loop-return" loopReturn.ref
  entry "collections" collections.ref
  entry "native-loop" nativeLoop.ref
  entry "map" mapped.ref
  entry "bind" bound.ref
  entry "fallback" recovered.ref
  entry "orelse" retried.ref
  entry "is-success" tested.ref
  collector "gc"

/-- The register-backed acceptance build. -/
@[datapack]
public def specimen : Spec := build { ns := "ledger", description := "Round ledger" } do
  root "ledger:stats" saved
  entries

/-- The same source program with the six-register scratch budget and stack-resident locals. -/
@[datapack]
public def stacked : Spec := build {
  ns := "ledgerstack", description := "Round ledger: stack locations", registerBudget := 6
} do
  root "ledgerstack:stats" saved
  entries

end Oria.Examples.RoundLedger
