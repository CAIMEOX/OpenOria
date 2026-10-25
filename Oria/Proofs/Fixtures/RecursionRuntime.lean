module

public import Oria
public import Oria.Datapack
public import Oria.Examples.Elaboration
meta import Oria
meta import Oria.Datapack
meta import Oria.Examples.Elaboration

namespace Oria.Proofs.Fixtures.RecursionRuntime

open Oria Oria.Std Oria.Datapack

@[mcfunction]
public def sum : Val Int32 → Prog .pure Int32 :=
  Prog.fix fun recur n => do
    if n <= 0 then return 0
    else
      let rest ← recur (n - 1)
      return n + rest

@[mcfunction]
public def fib : Val Int32 → Prog .pure Int32 :=
  Prog.fix fun recur n => do
    if n <= 1 then return n
    else
      let a ← recur (n - 1)
      let b ← recur (n - 2)
      return a + b

@[mcfunction]
public def captured (n base : Val Int32) : Prog .pure Int32 :=
  Prog.fix (fun (recur : Val Int32 → Prog .pure Int32) n => do
    if n <= 0 then return base
    else
      let rest ← recur (n - 1)
      return rest + base) n

@[mcfunction]
public def nested (n base : Val Int32) : Prog .pure Int32 :=
  Prog.fix (fun (outer : Val Int32 → Prog .pure Int32) n => do
    if n <= 0 then return base
    else
      let rest ← Prog.fix (fun (inner : Val Int32 → Prog .pure Int32) k => do
        if k <= 0 then outer (n - 1)
        else inner (k - 1)) (2 : Val Int32)
      return rest + n) n

private def objective : Command.Objective := "recursion_test.oria"

@[mcfunction]
public def countdown : Val Int32 → Prog (Grade.handled ⟨Req.none, Eff.scoreboardWrite⟩) Unit :=
  Prog.fix fun recur n => do
    if n <= 0 then return Val.unit
    else
      (Scoreboard.set (.named "#ticks") objective (.dynamic n)).ignore
      recur (n - 1)

@[mcfunction]
public def accumulate : Val Int32 → Val Int32 → Prog .pure Int32 :=
  Prog.fix fun recur n acc => do
    if n <= 0 then return acc
    else recur (n - 1) (acc + n)

@[mcfunction]
public def comparisons (x y : Val Int32) : Prog .pure Int32 := do
  let ordered := (x < y && x != y) || x == y
  if ordered && !(x > y) then return 1 else return 0

@[mcfunction]
private def shift (x : Val Int32) : Prog .pure Int32 := return x + 100

@[mcfunction]
public def acrossCall (x y : Val Int32) : Prog .pure Int32 := do
  let flag ← Prog.pure (x < y)
  let value ← shift.call x
  if flag then return value else return y

@[mcfunction]
private def run : Prog (Grade.handled ⟨Req.none, Eff.scoreboardWrite⟩) Unit := do
  let s ← sum.call 20
  (Scoreboard.set (.named "#sum") objective (.dynamic s)).ignore
  let f ← fib.call 9
  (Scoreboard.set (.named "#fib") objective (.dynamic f)).ignore
  let c ← captured.call 5 7
  (Scoreboard.set (.named "#captured") objective (.dynamic c)).ignore
  let n ← nested.call 4 10
  (Scoreboard.set (.named "#nested") objective (.dynamic n)).ignore
  let a ← accumulate.call 100 0
  (Scoreboard.set (.named "#accumulate") objective (.dynamic a)).ignore
  let lo ← comparisons.call (-2147483648) 2147483647
  let hi ← comparisons.call 2147483647 (-2147483648)
  let same ← comparisons.call 0 0
  (Scoreboard.set (.named "#comparisons") objective (.dynamic (lo * 100 + hi * 10 + same))).ignore
  let a ← acrossCall.call 1 2
  let b ← acrossCall.call 5 2
  (Scoreboard.set (.named "#call_predicate") objective (.dynamic (a * 10 + b))).ignore
  (Scoreboard.set (.named "#ticks") objective (.static 0)).ignore
  countdown.call 200

@[mcfunction]
private def elaboration := show Prog _ Unit from do
  let n ← Examples.Elaboration.shared.call 3
  Scoreboard.set (.named "#shared") objective n
  let c ← Examples.Elaboration.Counters.mk 2 3
  let state ← Examples.Elaboration.State.mk c 5
  let updated ← Examples.Elaboration.update.call state
  let before ← Examples.Elaboration.total.call state
  let after ← Examples.Elaboration.total.call updated
  Scoreboard.set (.named "#record_before") objective before
  Scoreboard.set (.named "#record_after") objective after
  let f ← Examples.Elaboration.fib.call 9
  let sum ← Examples.Elaboration.sum.call 20 7
  let host ← Examples.Elaboration.hostRecursion.call 4
  Scoreboard.set (.named "#local_fib") objective f
  Scoreboard.set (.named "#local_sum") objective sum
  Scoreboard.set (.named "#host_recursion") objective host
  let buf ← Nbt.alloc (Examples.Elaboration.Buffer.mk #[#[10, 20]] "initial")
  let n ← Examples.Elaboration.edit.call buf 0 1
  Scoreboard.set (.named "#native_index") objective n
  Nbt.store buf Nbt.Access.root (.storage "recursion_test:result") (.key "buffer")
  let hostIndex : Nat := 0
  buf.values[hostIndex][0] := 13
  let n ← buf.values[0][0]
  Scoreboard.set (.named "#host_index") objective n
  let n ← Examples.Elaboration.edit.call buf 0 1
  Scoreboard.set (.named "#native_equal_label") objective n
  buf.values[0][0] := (2147483647 : Val Int32)
  let n ← Examples.Elaboration.edit.call buf 0 0
  Scoreboard.set (.named "#native_overflow") objective n
  let n ← Examples.Elaboration.edit.call buf (-1) (-1)
  Scoreboard.set (.named "#native_negative") objective n
  buf.label := "literal $(p0): \"quoted\"\\\nnext"
  Nbt.store buf Examples.Elaboration.Buffer.Nbt.label
    (.storage "recursion_test:result") (.key "escaped")
  let failed ← (Examples.Elaboration.edit.call buf 0 99).isSuccess
  if failed then Prog.fail
  Scoreboard.set (.named "#native_failure") objective 1

@[datapack]
public def specimen : Spec := build { ns := "recursion_test", registerBudget := 8 } do
  entry "run" run.ref
  entry "elaboration" elaboration.ref

@[datapack]
public def allStack : Spec := build { ns := "recursion_zero", registerBudget := 6 } do
  entry "run" run.ref
  entry "elaboration" elaboration.ref

@[mcfunction]
private def sharedLet := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") "sharing.points"
  let x := n + 10
  (Scoreboard.set (.named "#output") "sharing.points" (x * x)).discard

@[mcfunction]
private def explicitBind := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") "sharing.points"
  let x ← Prog.pure (n + 10)
  (Scoreboard.set (.named "#output") "sharing.points" (x * x)).discard

@[datapack]
public def sharedArtifact : Spec := build {ns := "sharing"} do
  entry "run" sharedLet.ref

@[datapack]
public def boundArtifact : Spec := build {ns := "sharing"} do
  entry "run" explicitBind.ref

end Oria.Proofs.Fixtures.RecursionRuntime
