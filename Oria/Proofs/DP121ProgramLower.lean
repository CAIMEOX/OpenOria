module

import Oria.Std.Command.Declarations
import Oria.Std.Manifest
meta import Oria.Std.Manifest

import Oria.Meta.Collect
import Oria.Compiler.Lower.DP121.Program
import Oria.Compiler.Lower.Machine
import Oria.Meta.McFunction
public meta import Oria.Meta.Elab.ProgMatch
import Oria.Proofs.BackendUtil
import Oria.Proofs.Fixtures.MaybeI32
import Oria.Language.Failure
import Oria.Std.Scoreboard
import Oria.Std.Teleport
meta import Oria.Meta.Collect
meta import Oria.Compiler.Lower.DP121.Program
meta import Oria.Compiler.Lower.Machine
meta import Oria.Meta.McFunction
meta import Oria.Compiler.Program
meta import Oria.Proofs.Fixtures.MaybeI32
meta import Oria.Std

namespace Oria.Proofs.DP121ProgramLower

open Oria Oria.IR Oria.Program
open Oria.Proofs.Fixtures
open Oria.Target.DP121 Lean Lean.Elab Command

@[mcfunction]
private def arithmetic (x : Val Int32) : Prog .pure Int32 :=
  Prog.pure (((-x + 2) - 3) * 4)

@[mcfunction]
private def comparison (x y : Val Int32) : Prog .pure Bool :=
  Prog.pure (I32.le x y)

@[mcfunction]
private def identity (x : Val Int32) : Prog .pure Int32 :=
  Prog.pure x

private def points : Oria.Command.SyntaxToken :=
  .ofString "oria.points"

@[mcfunction]
private def readScore :
    Prog (Std.Scoreboard.readGrade .self) Int32 :=
  Std.Scoreboard.get .self (.ofToken points)

@[mcfunction]
private def chooseFlag (flag : Val Bool) : Prog .pure Int32 :=
  Prog.branch flag (Prog.pure 7) (Prog.pure 9)

@[mcfunction]
private def chooseValue (flag : Val Bool) (x y : Val Int32) : Prog .pure Int32 :=
  Prog.branch flag (Prog.pure (x + 1)) (Prog.pure (y + 2))

@[mcfunction]
private def chooseTag (choice : Val Choice) :
    Prog (Grade.joins [.pure, .pure, .pure]) Int32 :=
  do
    match choice with
    | .rock => return 1
    | .paper => return 2
    | .scissors => return 3

@[mcfunction]
private def increment (x : Val Int32) : Prog .pure Int32 :=
  Prog.pure (x + 1)

@[mcfunction]
private def invokeIncrement (x : Val Int32) : Prog .pure Int32 :=
  increment.call x

private def commandPosition (x : Val Int32) : Std.Command.Arg.Vec3 :=
  .world
    (.relative (.dynamic x))
    (.absolute (.static 80))
    (.relative (.static 0))

private def teleportGrade : Grade :=
  Std.Teleport.grade .self (commandPosition (I32.lit 0))

@[mcfunction]
private def teleportTail (x : Val Int32) : Prog teleportGrade Int32 :=
  Std.Teleport.to .self (commandPosition x)

private def setGrade : Grade :=
  Std.Scoreboard.writeGrade .self

private def setScore (x : Val Int32) : Prog setGrade Int32 :=
  Std.Scoreboard.set .self (.ofToken points) (.dynamic x)

@[mcfunction]
private def commandEffect (x : Val Int32) : Prog setGrade.handled Int32 :=
  Prog.bind (setScore x).ignore fun _ => Prog.pure x

@[mcfunction]
private def nativeCallee (x : Val Int32) : Prog setGrade Int32 :=
  setScore x

@[mcfunction]
private def nativeCallTail (x : Val Int32) : Prog setGrade Int32 :=
  nativeCallee.call x

@[mcfunction]
private def nativeCallEffect (x : Val Int32) : Prog setGrade.handled Int32 :=
  Prog.bind (nativeCallee.call x).ignore fun _ => Prog.pure x

@[mcfunction]
private def divide (x y : Val Int32) : Prog .failure Int32 := x / y

@[mcfunction]
private def add3 (x y z : Val Int32) : Prog .pure Int32 :=
  Prog.pure (x + y + z)

@[mcfunction]
private def invokeAdd3 (x y z : Val Int32) : Prog .pure Int32 :=
  add3.call x y z

private def config : Oria.Lower.DP121.Config := {
  resourceNamespace := .ofString "oria"
  objective := .ofToken (.ofString "oria.vm")
}

run_cmd do
  let ⟨_, machine⟩ ← BackendUtil.compile #[
      ⟨_, arithmetic.ref⟩,
      ⟨_, comparison.ref⟩,
      ⟨_, identity.ref⟩,
      ⟨_, readScore.ref⟩,
      ⟨_, chooseFlag.ref⟩,
      ⟨_, chooseValue.ref⟩,
      ⟨_, chooseTag.ref⟩,
      ⟨_, increment.ref⟩,
      ⟨_, invokeIncrement.ref⟩,
      ⟨_, teleportTail.ref⟩,
      ⟨_, commandEffect.ref⟩,
      ⟨_, nativeCallee.ref⟩,
      ⟨_, nativeCallTail.ref⟩,
      ⟨_, nativeCallEffect.ref⟩,
      ⟨_, divide.ref⟩,
      ⟨_, add3.ref⟩,
      ⟨_, invokeAdd3.ref⟩
    ]
  let .ok commands := Std.Manifest.commandCatalog
    | throwError "standard command catalogue did not build"
  let target ← match Oria.Lower.DP121.lower config machine commands with
    | .ok target => pure target
    | .error diagnostic =>
        throwError "scalar Machine program did not lower to DP121: {repr diagnostic}"

  -- Lowering every scalar entry point above must succeed, and the emitted function
  -- identities must stay unique so that the pack has exactly one file per function.
  unless target.functions.toList.map
      (fun ⟨_, definition⟩ => definition.ref.id.render) |>.Nodup do
    throwError "DP121 generated function identities were not unique"

end Oria.Proofs.DP121ProgramLower
