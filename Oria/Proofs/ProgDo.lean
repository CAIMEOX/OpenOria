module

import Oria.Std.Command.Declarations

public import Oria.Compiler.Definition
public import Oria.Meta.Elab.ProgDo
public import Oria.Meta.Elab.ProgMatch
import Oria.IR.Cont.Pretty
import Oria.IR.Tree.Pretty
import Oria.Proofs.McFunctionUtil
public import Oria.Std
meta import Oria.Compiler.Definition
meta import Oria.IR.Cont.Pretty
meta import Oria.IR.Tree.Pretty
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Std

namespace Oria.Proofs.ProgDo

open Oria
open Lean Lean.Elab Command
open Oria.Proofs.McFunctionUtil
open Oria.Std.Command.Arg

example : IO Nat := do
  pure 1

example : StateM Nat Nat := do
  get

example : Except String Nat := do
  pure 1

set_option backward.do.legacy false in
example : IO Nat := do
  pure 1

private def inferFromLater
    {A B : Type} (_first _later : A) (result : B) : B :=
  result

@[mcfunction]
private def postponedExpectedType (x : Val Int32) : Prog .pure Int32 :=
  inferFromLater
    (do return x)
    (Prog.pure x)
    (Prog.pure x)

@[mcfunction]
private def oneBind (x : Val Int32) : Prog .pure Int32 :=
  do
    let y ← Prog.pure x
    return y

@[mcfunction]
private def bindThenAdd (x : Val Int32) : Prog .pure Int32 :=
  do
    let y ← Prog.pure x
    return y + 1

@[mcfunction]
private def bindThenAddExplicit (x : Val Int32) : Prog .pure Int32 :=
  Prog.bind (Prog.pure x) fun y =>
    Prog.pure (y + 1)

@[mcfunction]
private def hostLet (x : Val Int32) : Prog .pure Int32 :=
  do
    let host : Int32 := 7
    return x + I32.lit host

@[mcfunction]
private def tailProgram (x : Val Int32) : Prog .pure Int32 :=
  do
    let y := x + 1
    Prog.pure y

@[mcfunction]
private def dynamicTailIf
    (condition : Val Bool)
    (left right : Val Int32) : Prog .pure Int32 :=
  do
    if condition then
      return left
    else
      return right

@[mcfunction]
private def dynamicIfThenAdd
    (condition : Val Bool)
    (left right : Val Int32) : Prog .pure Int32 :=
  do
    if condition then
      Prog.pure Val.unit
    else
      Prog.pure Val.unit
    return left + right

@[mcfunction]
private def dynamicIfThenAddExplicit
    (condition : Val Bool)
    (left right : Val Int32) : Prog .pure Int32 :=
  Prog.bind
    (Prog.branch condition (Prog.pure Val.unit) (Prog.pure Val.unit))
    fun _ => Prog.pure (left + right)

@[mcfunction]
private def hostBoolIf
    (left right : Val Int32) : Prog .pure Int32 :=
  do
    let chooseLeft : Bool := true
    if chooseLeft then
      return left
    else
      return right

@[mcfunction]
private def hostBoolIfThenAdd
    (left right : Val Int32) : Prog .pure Int32 :=
  do
    let chooseLeft : Bool := true
    if chooseLeft then
      Prog.pure Val.unit
    else
      Prog.pure Val.unit
    return left + right

@[mcfunction]
private def hostPropIf
    (left right : Val Int32) : Prog .pure Int32 :=
  do
    let chooseLeft : Prop := True
    if chooseLeft then
      return left
    else
      return right

private def relativePosition (x : Val Int32) : Vec3 :=
  .world
    (.relative (.dynamic x))
    (.absolute (.static 80))
    (.relative (.static 0))

private def teleportGrade : Grade :=
  Std.Teleport.grade .self (relativePosition (I32.lit 0))

private def teleport (x : Val Int32) :
    Prog teleportGrade Int32 :=
  Std.Teleport.to .self (relativePosition x)

private def scoreboardGrade : Grade :=
  Std.Scoreboard.writeGrade (.named (.ofString "#oria"))

private def scoreboardSet :
    Prog scoreboardGrade Int32 :=
  Std.Scoreboard.set
    (.named (.ofString "#oria"))
    (.ofString "oria.test")
    (.static 1)

@[mcfunction]
private def twoGrades (x : Val Int32) :
    Prog (teleportGrade.seq scoreboardGrade).handled Int32 :=
  do
    (teleport x).ignore
    scoreboardSet.ignore
    return x

@[mcfunction]
private def twoGradesExplicit (x : Val Int32) :
    Prog (teleportGrade.seq scoreboardGrade).handled Int32 :=
  Prog.bind (Prog.ignore (teleport x)) fun _ =>
    Prog.bind (Prog.ignore scoreboardSet) fun _ =>
      Prog.pure x

private def inferAction {g : Grade} {A : Type} {a : ObjTy} [Object A a]
    (action : Prog g A) : Prog g A := action

@[mcfunction]
private def inferredTail := inferAction do
  Std.Scoreboard.get .self "points"

example : inferredTail.signature.result = .i32 := rfl

private def comparePipelines
    (leftName rightName : Lean.Name)
    (routes : List Oria.Command.Decl := []) : CommandElabM Unit := do
  let left ← elaborate leftName
  let right ← elaborate rightName
  let leftTree := left.definition.pretty 100
  let rightTree := right.definition.pretty 100
  unless leftTree == rightTree do
    throwError "ordinary `do` and explicit bind produced different Tree definitions:\nleft:\n{leftTree}\nright:\n{rightTree}"
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the ordinary-do object catalog"
  let .ok commands := Oria.Command.Catalog.build routes
    | throwError "failed to build the ordinary-do command catalog"
  let .ok functions := Function.Catalog.build [left, right]
    | throwError "failed to build the ordinary-do function catalog"
  let .ok leftCont := Compiler.compile functions objects commands left
    | throwError "failed to lower the ordinary-do definition"
  let .ok rightCont := Compiler.compile functions objects commands right
    | throwError "failed to lower the explicit-bind definition"
  let leftCont := leftCont.pretty 100
  let rightCont := rightCont.pretty 100
  unless leftCont == rightCont do
    throwError "ordinary `do` and explicit bind produced different Cont definitions:\nleft:\n{leftCont}\nright:\n{rightCont}"

run_cmd comparePipelines ``bindThenAdd ``bindThenAddExplicit

run_cmd comparePipelines ``dynamicIfThenAdd ``dynamicIfThenAddExplicit

run_cmd comparePipelines ``twoGrades ``twoGradesExplicit [
  Std.Command.Declarations.teleport.declaration,
  Std.Command.Declarations.scoreSet.declaration
]

run_cmd
  let dynamic ← elaborate ``dynamicTailIf
  let host ← elaborate ``hostBoolIf
  let expected :=
    "fn (%0 : I32, %1 : I32) -> I32 !{req=0, eff=0} {\n  return %0\n}"
  unless host.definition.pretty 100 == expected do
    throwError "host `Bool` if did not reduce during quotation:\n{host.definition.pretty 100}"

run_cmd
  let elaborated ← elaborate ``dynamicIfThenAdd
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the dynamic-if object catalog"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the dynamic-if command catalog"
  let .ok functions := Function.Catalog.build [elaborated]
    | throwError "failed to build the dynamic-if function catalog"
  let .ok lowered := Compiler.compile functions objects commands elaborated
    | throwError "failed to lower the dynamic-if definition"
  let rendered := lowered.pretty 100
  unless (rendered.splitOn "join @").length == 2 do
    throwError "dynamic non-tail if did not lower to exactly one shared continuation:\n{rendered}"

/--
error: Oria `do` supports only a plain condition in `if`; use explicit object elimination for pattern tests
-/
#guard_msgs(error, substring := true) in
private def ifLetCondition (x : Val Int32) : Prog .pure Int32 :=
  do
    if let true := true then
      return x
    else
      return x

/--
error: object `if` branches return incompatible value types
-/
#guard_msgs in
private def ifWithoutElse
    (condition : Val Bool) (x : Val Int32) : Prog .pure Int32 :=
  do
    if condition then
      return x

/--
error: Oria `do` does not support dependent `if`
-/
#guard_msgs(error, substring := true) in
private def dependentIf (x : Val Int32) : Prog .pure Int32 :=
  do
    if h : True then
      return x
    else
      return x

/--
error: Oria `do` `if` condition must have type `Bool`, `Prop`, or `Val Bool`
-/
#guard_msgs(error, substring := true) in
private def unsupportedCondition {C : Type} (condition : C) (x : Val Int32) : Prog .pure Int32 :=
  do
    if condition then
      return x
    else
      return x

/--
error: Oria `do` cannot infer the `if` condition type; add a `Bool`, `Prop`, or `Val Bool` annotation
-/
#guard_msgs(error, substring := true) in
private def unresolvedCondition (x : Val Int32) : Prog .pure Int32 :=
  do
    if _ then
      return x
    else
      return x

@[mcfunction]
private def branchEarlyReturn
    (condition : Val Bool) (x : Val Int32) : Prog .pure Int32 :=
  do
    if condition then
      return x
    else
      Prog.pure Val.unit
    return x

/--
error: Oria `do` does not support mutable bindings
-/
#guard_msgs(error, substring := true) in
private def mutableBinding (x : Val Int32) : Prog .pure Int32 :=
  do
    let mut y := x
    return y

private def explicitDefaultLetConfig (x : Val Int32) : Prog .pure Int32 :=
  do
    let -zeta y := x
    return y

/--
error: Oria `do` does not support configured `let` bindings
-/
#guard_msgs in
private def configuredLetBinding (x : Val Int32) : Prog .pure Int32 :=
  do
    let +zeta y := x
    return y

@[mcfunction]
private def patternBind (x : Val (Option Int32)) : Prog .pure Int32 := do
  let .some y ← Prog.pure x | return 0
  return y

/-- warning: This `do` element and its control-flow region are dead code. Consider removing it. -/
#guard_msgs(warning, substring := true) in
private def earlyReturn (x : Val Int32) : Prog .pure Int32 :=
  do
    return x
    return x

@[mcfunction]
private def bareStatement (x : Val Int32) : Prog .pure Int32 :=
  do
    Prog.pure x
    return x

@[mcfunction]
private def forLoop (x : Val Int32) : Prog .pure Int32 :=
  do
    for _ in [1] do
      Prog.pure Val.unit
    return x

@[mcfunction]
private def hostHelpers (x : Val Int32) : Prog .pure Int32 := do
  let twice (v : Val Int32) : Val Int32 := v + v
  let (offset, scale) := ((3 : Int32), (2 : Int32))
  return twice x + I32.lit offset * I32.lit scale

/--
error: Oria `do` grade mismatch
inferred: requires {executor} effects {scoreboardRead, failure}
declared: requires {} effects {}
-/
#guard_msgs(error, substring := true) in
private def insufficientGrade : Prog .pure Int32 := do
  let n ← Std.Scoreboard.get .self "points"
  return n

/--
error: Oria `do` does not support loops
-/
#guard_msgs(error, substring := true) in
private def whileLoop (x : Val Int32) : Prog .pure Int32 :=
  do
    while true do
      return ()
    return x

@[mcfunction]
private def tryBlock (x : Val Int32) : Prog .pure Int32 :=
  do
    try
      Prog.pure x
    catch _ =>
      Prog.pure x
    return x

/--
error: `break` must be nested inside a loop
-/
#guard_msgs(error, substring := true) in
private def breakBlock (x : Val Int32) : Prog .pure Int32 :=
  do
    break
    return x

/--
error: `continue` must be nested inside a loop
-/
#guard_msgs(error, substring := true) in
private def continueBlock (x : Val Int32) : Prog .pure Int32 :=
  do
    continue
    return x

end Oria.Proofs.ProgDo
