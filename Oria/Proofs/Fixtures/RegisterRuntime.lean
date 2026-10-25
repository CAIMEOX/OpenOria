module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.RegisterRuntime

open Oria Oria.Std Oria.Datapack

@[mcfunction]
public def sum20 (a b c d e f g h i j k l m n o p q r s t : Val Int32) : Prog .pure Int32 :=
  Prog.pure (a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s + t)

@[mcfunction]
public def inner (a b : Val Int32) : Prog .pure Int32 := Prog.pure (a * b + a)

@[mcfunction]
public def outer (n : Val Int32) : Prog .pure Int32 := do
  let old ← Prog.pure (n + 5)
  let value ← inner.call n (n + 1)
  return old + value

@[mcfunction]
public def mix (n : Val Int32) : Prog .pure Int32 := do
  let a ← Prog.pure (n + 1)
  let b ← Prog.pure (n + 2)
  return a * b

@[mcfunction]
public def preserved (n : Val Int32) : Prog .pure Int32 := do
  let old ← Prog.pure (n + 5)
  let arg ← Prog.pure (n + 1)
  let value ← mix.call arg
  return old + value

private def points : Command.Objective := "register_test.oria"

@[mcfunction]
private def run : Prog (Grade.handled ⟨Req.none, Eff.scoreboardWrite⟩) Unit := do
  let sum ← sum20.call 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
  (Scoreboard.set (.named "#sum") points (.dynamic sum)).ignore
  let value ← outer.call 4
  (Scoreboard.set (.named "#call") points (.dynamic value)).ignore
  let value ← preserved.call 4
  (Scoreboard.set (.named "#saved") points (.dynamic value)).ignore

@[datapack]
public def specimen : Spec := build {
    ns := "register_test"
    registerBudget := 8
  } do
    entry "run" run.ref

@[datapack]
public def allStack : Spec := build {
    ns := "register_zero"
    registerBudget := 6
  } do
    entry "run" run.ref

end Oria.Proofs.Fixtures.RegisterRuntime
