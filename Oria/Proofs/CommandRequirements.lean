module

import Oria
import Oria.Std.Command.Declarations
meta import Oria

namespace Oria.Proofs.CommandRequirements

open Oria.Std Oria.Std.Command.Arg

private def points : Command.Objective := .ofString "coeffects.points"

@[mcfunction]
private def readSelf : Prog ⟨Req.executor, Eff.scoreboardRead ||| Eff.failure⟩ Int32 :=
  Scoreboard.get .self points

@[mcfunction]
private def readNamed : Prog ⟨Req.none, Eff.scoreboardRead ||| Eff.failure⟩ Int32 :=
  Scoreboard.get (.named (.ofString "#shared")) points

example : readSelf.signature.grade.req = Req.executor := rfl
example : readNamed.signature.grade.req = Req.none := rfl

private def named := Std.Command.Declarations.scoreGet.call <|
  .cons (Command.encode (ScoreHolder.named (.ofString "#shared"))) <|
  .cons (Command.encode points) .nil

#guard named.grade.req == Req.none

example {v w : ObjTy → Type} {sig : Command.Signature} (request : Command.Call v sig)
    (f : ∀ {a}, v a → w a) :
    (request.map f).grade = request.grade := by simp

end Oria.Proofs.CommandRequirements
