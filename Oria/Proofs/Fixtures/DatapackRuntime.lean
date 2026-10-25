module

public import Oria
public import Oria.Datapack
import Oria.Proofs.Fixtures.Datapack
import Oria.Std.Manifest
meta import Oria
meta import Oria.Datapack
meta import Oria.Proofs.Fixtures.Datapack

namespace Oria.Proofs.Fixtures.DatapackRuntime

open Oria Oria.Std Oria.Datapack

private def counterSig : Oria.Command.Signature :=
  { schema := [], req := Req.none, eff := Eff.scoreboardWrite }

private def counter (key : Lean.Name) (op holder n : Oria.Command.SyntaxToken) :
    Oria.Command.Ref counterSig :=
  { key, template.parts :=
      ((["scoreboard", "players", op, holder,
        "acceptance.oria", n] : List Oria.Command.SyntaxToken).map
          Oria.Command.TemplatePart.token).intersperse .space }

private def first := counter `oria.test.first "set" "#order" "10"
private def next := counter `oria.test.next "add" "#order" "1"
private def loaded := counter `oria.test.loaded "add" "#loads" "1"
private def ticked := counter `oria.test.tick "add" "#ticks" "1"

@[mcfunction]
private def setup : Prog (Grade.handled counterSig.grade) Unit := (Command.emit (first.call .nil)).ignore

@[mcfunction]
private def step : Prog (Grade.handled counterSig.grade) Unit := (Command.emit (next.call .nil)).ignore

@[mcfunction]
private def countLoad : Prog (Grade.handled counterSig.grade) Unit := (Command.emit (loaded.call .nil)).ignore

@[mcfunction]
private def countTick : Prog (Grade.handled counterSig.grade) Unit := (Command.emit (ticked.call .nil)).ignore

@[mcfunction]
private def moveBy (x : Val Int32) : Prog (Grade.handled ⟨11#8, 67#16⟩) Unit := do
  (Teleport.to .self
    (.world (.relative (.dynamic x)) (.absolute (.static 80))
      (.relative (.static 0)))).ignore

@[mcfunction]
private def dynamic : Prog (Grade.handled ⟨11#8, 67#16⟩) Unit := do
  let x ← Fixtures.Datapack.increment.call 7
  moveBy.call x

@[mcfunction]
private def home : Prog (Grade.handled ⟨11#8, 67#16⟩) Unit :=
  (Teleport.to .self
    (.world (.relative (.static 1)) (.absolute (.static 80))
      (.relative (.static 3)))).ignore

public inductive Chain (A : Type) where
  | nil
  | cons (head : A) (tail : Chain A)
  deriving Oria.Object

public structure Summary where
  first : Int32
  padding : Unit
  observed : Option Int32
  deriving Oria.Object

@[mcfunction]
private def head (value : Val (Chain Int32)) : Prog .pure Int32 := do
  match value with
  | .nil => return -10
  | .cons first _ => return first

@[mcfunction]
private def summarize (value : Val Summary) : Prog .pure Int32 := do
  match value with
  | .mk first _ (.some second) => return first + second
  | .mk first _ .none => return first - 1

private def points : Command.Objective := "acceptance.oria"
private def input := Scoreboard.get (.named "#input") points

@[mcfunction]
private def objectResult : Prog ⟨Req.none, Eff.scoreboardRead⟩ Int32 := do
  let tail ← Chain.Obj.Ctor.nil (A := Int32)
  let chain ← Chain.Obj.Ctor.cons (41 : Val Int32) tail
  let first ← head.call chain
  let observed ← Prog.attempt input
  let record ← Summary.Obj.Ctor.mk first Val.unit observed
  summarize.call record

@[mcfunction]
private def payload : Prog (Grade.handled ((⟨Req.none, Eff.scoreboardRead ||| Eff.scoreboardWrite⟩ : Grade))) Unit := do
  let result ← objectResult.call
  (Scoreboard.set (.named "#payload") points (.dynamic result)).ignore

@[mcfunction]
private def commandChain : Prog ((⟨Req.none, Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure⟩ : Grade)) Int32 := do
  let value ← input
  Scoreboard.set (.named "#continued") points (.dynamic value)
  return value + 1

@[mcfunction]
private def fallible : Prog (Grade.handled ((⟨Req.none, Eff.scoreboardRead ||| Eff.scoreboardWrite⟩ : Grade))) Unit :=
  commandChain.call.ignore

@[mcfunction]
private def discarded : Prog (Grade.handled ((⟨Req.none, Eff.scoreboardRead ||| Eff.scoreboardWrite⟩ : Grade))) Unit := do
  input.ignore
  (Scoreboard.set (.named "#continued") points (.static 17)).ignore

@[datapack]
public def specimen : Spec :=
  build {
    ns := "acceptance"
    description := "Oria datapack runtime acceptance"
    commands := some (Std.Manifest.commandDeclarations ++
      [first.declaration, next.declaration, loaded.declaration, ticked.declaration])
  } do
    entry "home" home.ref
    entry "home.v1" home.ref
    entry "dynamic" dynamic.ref
    entry "payload" payload.ref
    entry "fallible" fallible.ref
    entry "discarded" discarded.ref
    onLoad setup.ref
    onLoad step.ref
    onLoad step.ref
    onLoad countLoad.ref
    onTick countTick.ref

end Oria.Proofs.Fixtures.DatapackRuntime
