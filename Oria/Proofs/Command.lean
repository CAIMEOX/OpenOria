module

import Oria.Std.Command.Declarations

public import Oria.Proofs.McFunctionUtil
import Oria.Command.Catalog
import Oria.IR.Cont.Pretty
import Oria.IR.Tree.Syntax
import Oria.Compiler.Lower.ANF
import Oria.IR.Catalog.Object
import Oria.Std
import Oria.Language.Failure
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Command.Catalog
meta import Oria.IR.Cont.Pretty
meta import Oria.Compiler.Lower.ANF
meta import Oria.IR.Catalog.Object
meta import Oria.Std

open Oria.Command (Objective ScoreOp)

namespace Oria.Proofs.Command

open Oria Oria.IR
open Lean Lean.Elab Command
open Oria.Std.Command.Arg
open Oria.Proofs.McFunctionUtil

#guard (Command.SyntaxToken.parse "points").isOk

#guard
  match Command.SyntaxToken.parse "bad objective" with
  | .error _ => true
  | .ok _ => false

#guard (ScoreHolderName.parse "player").isOk

#guard
  match ScoreHolderName.parse "@s" with
  | .error _ => true
  | .ok _ => false

#guard
  match ScoreHolderName.parse "*" with
  | .error _ => true
  | .ok _ => false

example {f : ObjTy → Type} {sig : Command.Signature}
    (request : Command.Call f sig) :
    request.map (fun value => value) = request :=
  Command.Call.map_id request

example {f g h : ObjTy → Type} {sig : Command.Signature}
    (left : ∀ {a}, f a → g a)
    (right : ∀ {a}, g a → h a)
    (request : Command.Call f sig) :
    (request.map left).map right = request.map (fun value => right (left value)) :=
  Command.Call.map_comp left right request

example {f : ObjTy → Type} (fragment : Command.Fragment f) :
    fragment.map (fun value => value) = fragment :=
  Command.Fragment.map_id fragment

example {f g h : ObjTy → Type}
    (left : ∀ {a}, f a → g a)
    (right : ∀ {a}, g a → h a)
    (fragment : Command.Fragment f) :
    (fragment.map left).map right = fragment.map (fun value => right (left value)) :=
  Command.Fragment.map_comp left right fragment

example {route : Command.Signature} (request : Command.Call IR.Tree.Expr route) :
    IR.Tree.Prim request.grade .i32 :=
  .command request

example : Prog (Grade.handled .pure) Unit :=
  Prog.ignore (Prog.pure (I32.lit 1))

private def staticPosition : Vec3 :=
  .world
    (.absolute (.static 10))
    (.absolute (.static 80))
    (.relative (.static 0))

example : (Command.encode staticPosition).holeCount = 0 := rfl

private def mixedPosition (x : Val Int32) : Vec3 :=
  .world
    (.relative (.dynamic x))
    (.absolute (.static 80))
    (.relative (.static 0))

example (x : Val Int32) :
    (Command.encode (mixedPosition x)).holeCount = 1 := rfl

example (x y z : Val Int32) :
    (Command.encode <|
      Vec3.world
        (.absolute (.dynamic x))
        (.relative (.dynamic y))
        (.absolute (.dynamic z))).holeCount = 3 := rfl

private def teleportRequest (x : Val Int32) :=
  Std.Command.Declarations.teleport.call <|
    .cons (Command.encode (.self : Target)) <|
      .cons (Command.encode (mixedPosition x)) .nil

private def teleportGrade : Grade :=
  (teleportRequest (I32.lit 0)).grade

private theorem teleportGrade_eq (x : Val Int32) :
    (teleportRequest x).grade = teleportGrade := rfl

private def castGrade
    {A : Type} {a : ObjTy} [Object A a]
    {left right : Grade} (equal : left = right) (program : Prog left A) : Prog right A :=
  equal ▸ program

@[mcfunction]
private def teleport (x : Val Int32) :
    Prog teleportGrade Int32 :=
  castGrade (teleportGrade_eq x) <|
    Command.emit (teleportRequest x)

example (x : Val Int32) :
    Prog (Std.Teleport.grade .self (mixedPosition x)) Int32 :=
  Std.Teleport.to .self (mixedPosition x)

run_cmd
  let elaborated ← elaborate ``teleport
  unless elaborated.signature == teleport.signature do
    throwError "teleport recipe has the wrong generated signature"
  match ObjectCatalog.build [] with
  | .error diagnostic =>
      throwError "failed to build the primitive object catalog: {repr diagnostic}"
  | .ok catalog =>
      unless (catalog.link elaborated.definition).isOk do
        throwError "teleport failed object linking"

@[mcfunction]
private def ignoredTeleport (x : Val Int32) : Prog (Grade.handled teleportGrade) Unit :=
  Prog.ignore <| castGrade (teleportGrade_eq x) <|
    Command.emit (teleportRequest x)

@[mcfunction]
private def observedTeleport (x : Val Int32) :
    Prog teleportGrade.handled Int32 :=
  (castGrade (teleportGrade_eq x) (Command.emit (teleportRequest x))).getD (-1)

private def holder (name : ScoreHolderName) : ScoreHolder :=
  .named name

private def objective (token : Command.SyntaxToken) : Objective :=
  .ofToken token

private def points : Command.SyntaxToken :=
  .ofString "points"

private def player : ScoreHolderName :=
  .ofString "player"

example (player : ScoreHolderName) (points : Command.SyntaxToken) :
    Prog (Std.Scoreboard.readGrade (holder player)) Int32 :=
  Std.Scoreboard.get (holder player) (objective points)

example :
    (Std.Command.Declarations.scoreGet.call <|
      .cons (Command.encode (holder player)) <|
        .cons (Command.encode (objective points)) .nil).holeCount = 0 := by native_decide

example (player : ScoreHolderName) (points : Command.SyntaxToken)
    (value : Val Int32) :
    Prog (Std.Scoreboard.writeGrade (holder player)) Int32 :=
  Std.Scoreboard.set
    (holder player)
    (objective points)
    (.dynamic value)

example :
    (Std.Command.Declarations.scoreSet.call <|
      .cons (Command.encode (holder player)) <|
        .cons (Command.encode (objective points)) <|
          .cons (Command.encode (.dynamic (I32.lit 5) : Scalar)) .nil).holeCount = 1 := by native_decide

private def slot
    (holderName : ScoreHolderName)
    (objectiveToken : Command.SyntaxToken) : ScoreSlot :=
  { holder := .named holderName, objective := .ofToken objectiveToken }

example (left right : ScoreHolderName) (points : Command.SyntaxToken) :
    Prog (Std.Scoreboard.operationGrade (slot left points) (slot right points)) Int32 :=
  Std.Scoreboard.operation
    (slot left points)
    (.add : ScoreOp)
    (slot right points)

example :
    (Std.Command.Declarations.scoreOperation.call <|
      .cons (Command.encode (slot player points)) <|
        .cons (Command.encode (.swap : ScoreOp)) <|
          .cons (Command.encode (slot player points)) .nil).holeCount = 0 := by native_decide

example : (Std.Scoreboard.operationGrade (slot player points) (slot player points)).eff =
    Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.failure := rfl

example :
    (Std.Scoreboard.operationGrade (slot player points) (slot player points)).req = Req.none := rfl

private def encodedOperation (operation : ScoreOp) : Option String :=
  match (Command.encode operation).fragment.segments with
  | [Command.Segment.token value] => some value.text
  | _ => none

#guard
  ([.assign, .add, .subtract, .multiply, .divide, .modulo, .minimum, .maximum, .swap] :
      List ScoreOp).map encodedOperation ==
    [some "=", some "+=", some "-=", some "*=", some "/=", some "%=", some "<", some ">",
      some "><"]

private def commandCatalog : Except Diagnostic Command.Catalog :=
  Command.Catalog.build [
    Std.Command.Declarations.teleport.declaration,
    Std.Command.Declarations.scoreGet.declaration,
    Std.Command.Declarations.scoreSet.declaration,
    Std.Command.Declarations.scoreOperation.declaration
  ]

#guard (Command.Catalog.build Std.Command.Declarations.all).isOk

#guard
  match Command.Catalog.build [
      Std.Command.Declarations.teleport.declaration,
      Std.Command.Declarations.teleport.declaration
    ] with
  | .error (.duplicateCommand key) => key == Std.Command.Declarations.teleport.key
  | _ => false

#guard
  let invalidTemplate : Command.Template [(Oria.Command.ArgCodec.key (A := Oria.Std.Command.Arg.Target)), (Oria.Command.ArgCodec.key (A := Oria.Std.Command.Arg.Vec3))] :=
    { parts := [.token (.ofString "teleport")] }
  let invalid : Command.Decl :=
    { key := Std.Command.Declarations.teleport.key
      sig := Std.Command.Declarations.teleport.signature
      template := invalidTemplate }
  match Command.Catalog.build [invalid] with
  | .error (.invalidCommandTemplate key) => key == Std.Command.Declarations.teleport.key
  | _ => false

#guard
  let invalidTemplate : Command.Template [(Oria.Command.ArgCodec.key (A := Oria.Std.Command.Arg.Target)), (Oria.Command.ArgCodec.key (A := Oria.Std.Command.Arg.Vec3))] :=
    { parts := [
      .slot ⟨0, by simp⟩,
      .space,
      .slot ⟨0, by simp⟩
    ] }
  let invalid : Command.Decl :=
    { key := Std.Command.Declarations.teleport.key
      sig := Std.Command.Declarations.teleport.signature
      template := invalidTemplate }
  match Command.Catalog.build [invalid] with
  | .error (.invalidCommandTemplate key) => key == Std.Command.Declarations.teleport.key
  | _ => false

run_cmd
  let elaborated ← elaborate ``teleport
  match commandCatalog, ObjectCatalog.build [] with
  | .ok commands, .ok objects =>
      match objects.link elaborated.definition with
      | .error diagnostic =>
          throwError "teleport failed object linking: {repr diagnostic}"
      | .ok objectLinked =>
          unless (commands.link objectLinked).isOk do
            throwError "teleport failed command linking"
          match Command.Catalog.build [] with
          | .error diagnostic =>
              throwError "failed to build the empty command catalog: {repr diagnostic}"
          | .ok empty =>
              match empty.link objectLinked with
              | .error (.unknownCommand key) =>
                  unless key == Std.Command.Declarations.teleport.key do
                    throwError "empty catalog rejected the wrong command route"
              | _ => throwError "empty catalog unexpectedly linked teleport"
  | .error diagnostic, _ =>
      throwError "failed to build the command catalog: {repr diagnostic}"
  | _, .error diagnostic =>
      throwError "failed to build the primitive object catalog: {repr diagnostic}"

private def swappedTeleportTemplate : Command.Template [(Oria.Command.ArgCodec.key (A := Oria.Std.Command.Arg.Target)), (Oria.Command.ArgCodec.key (A := Oria.Std.Command.Arg.Vec3))] :=
  { parts := [
    .token (.ofString "teleport"),
    .space,
    .slot ⟨1, by simp⟩,
    .space,
    .slot ⟨0, by simp⟩
  ] }

private def swappedTemplateRequest (x : Val Int32) :
    Command.Call EncodedVal Std.Command.Declarations.teleport.signature :=
  { ref := ⟨Std.Command.Declarations.teleport.key, swappedTeleportTemplate, none⟩
    args := (teleportRequest x).args }

private def swappedTemplateGrade : Grade :=
  (swappedTemplateRequest (I32.lit 0)).grade

@[mcfunction]
private def swappedTemplate (x : Val Int32) :
    Prog swappedTemplateGrade Int32 :=
  Command.emit (swappedTemplateRequest x)

run_cmd
  let elaborated ← elaborate ``swappedTemplate
  match commandCatalog, ObjectCatalog.build [] with
  | .ok commands, .ok objects =>
      match objects.link elaborated.definition with
      | .error diagnostic =>
          throwError "swapped template failed object linking: {repr diagnostic}"
      | .ok objectLinked =>
          match commands.link objectLinked with
          | .error (.commandTemplateMismatch key) =>
              unless key == Std.Command.Declarations.teleport.key do
                throwError "swapped template reported the wrong route"
          | _ => throwError "swapped command template unexpectedly linked"
  | .error diagnostic, _ =>
      throwError "failed to build the command catalog: {repr diagnostic}"
  | _, .error diagnostic =>
      throwError "failed to build the primitive object catalog: {repr diagnostic}"

private def fakeTeleportSig : Command.Signature :=
  { Std.Command.Declarations.teleport.signature with eff := Eff.none }

private def fakeTeleportRoute : Command.Ref fakeTeleportSig :=
  ⟨Std.Command.Declarations.teleport.key, Std.Command.Declarations.teleport.template, none⟩

private def fakeTeleportRequest (x : Val Int32) :
    Command.Call EncodedVal fakeTeleportSig :=
  { ref := fakeTeleportRoute
    args := (teleportRequest x).args }

private def fakeTeleportGrade : Grade :=
  (fakeTeleportRequest (I32.lit 0)).grade

private theorem fakeTeleportGrade_eq (x : Val Int32) :
    (fakeTeleportRequest x).grade = fakeTeleportGrade := rfl

@[mcfunction]
private def fakeTeleport (x : Val Int32) :
    Prog fakeTeleportGrade Int32 :=
  castGrade (fakeTeleportGrade_eq x) <|
    Command.emit (fakeTeleportRequest x)

run_cmd
  let elaborated ← elaborate ``fakeTeleport
  match commandCatalog, ObjectCatalog.build [] with
  | .ok commands, .ok objects =>
      match objects.link elaborated.definition with
      | .error diagnostic =>
          throwError "fake teleport failed object linking: {repr diagnostic}"
      | .ok objectLinked =>
          match commands.link objectLinked with
          | .error (.commandSignatureMismatch key) =>
              unless key == Std.Command.Declarations.teleport.key do
                throwError "fake teleport reported the wrong route"
          | _ => throwError "route-signature mismatch unexpectedly linked"
  | .error diagnostic, _ =>
      throwError "failed to build the command catalog: {repr diagnostic}"
  | _, .error diagnostic =>
      throwError "failed to build the primitive object catalog: {repr diagnostic}"

end Oria.Proofs.Command
