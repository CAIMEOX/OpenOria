module

import Oria.Std.Command.Declarations

import Oria.Command.Catalog
import Oria.Proofs.McFunctionUtil
import Oria.Std
meta import Oria.Command.Catalog
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Std

namespace Oria.Proofs.TreeCommandCatalog

open Oria Oria.IR
open Lean Lean.Elab Command
open Oria.Proofs.McFunctionUtil
open Oria.Std.Command.Arg

private def mixedPosition (x : Val Int32) : Vec3 :=
  .world
    (.relative (.dynamic x))
    (.absolute (.static 80))
    (.relative (.static 0))

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
private def teleport (x : Val Int32) : Prog teleportGrade Int32 :=
  castGrade (teleportGrade_eq x) <|
    Command.emit (teleportRequest x)

private def commandCatalog : Except Diagnostic Command.Catalog :=
  Command.Catalog.build [Std.Command.Declarations.teleport.declaration]

run_cmd
  let definition := (← elaborate ``teleport).definition
  let objects ←
    match ObjectCatalog.build [] with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build the primitive object catalog: {repr diagnostic}"
  let objectLinked ←
    match objects.link definition with
    | .ok linked => pure linked
    | .error diagnostic =>
        throwError "teleport failed object linking: {repr diagnostic}"
  let commands ←
    match commandCatalog with
    | .ok catalog => pure catalog
    | .error diagnostic =>
        throwError "failed to build the command catalog: {repr diagnostic}"
  unless (commands.link objectLinked).isOk do
    throwError "valid Teleport Tree failed command linking"

@[mcfunction]
private def boundTeleport (x : Val Int32) :
    Prog (teleportGrade.seq Grade.pure) Int32 :=
  Prog.bind
    (castGrade (teleportGrade_eq x) <|
      Command.emit (teleportRequest x))
    fun result => Prog.pure result

run_cmd
  let definition := (← elaborate ``boundTeleport).definition
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link definition
    | throwError "bound teleport failed object linking"
  let .ok commands := commandCatalog
    | throwError "failed to build the command catalog"
  unless (commands.link objectLinked).isOk do
    throwError "command in the value side of Tree bind failed command linking"

run_cmd
  let definition := (← elaborate ``teleport).definition
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link definition
    | throwError "teleport failed object linking"
  let .ok commands := Command.Catalog.build []
    | throwError "failed to build the empty command catalog"
  match commands.link objectLinked with
  | .error (.unknownCommand key) =>
      unless key == Std.Command.Declarations.teleport.key do
        throwError "unknown-route diagnostic carried the wrong key"
  | .error diagnostic =>
      throwError "expected unknown-route diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "unknown Tree command route unexpectedly linked"

private def unknownTeleportRequest (x : Val Int32) :
    Command.Call EncodedVal Std.Command.Declarations.teleport.signature :=
  { ref := ⟨`proof.unknown_teleport, Std.Command.Declarations.teleport.template, none⟩
    args := (teleportRequest x).args }

private def unknownTeleportGrade : Grade :=
  (unknownTeleportRequest (I32.lit 0)).grade

private theorem unknownTeleportGrade_eq (x : Val Int32) :
    (unknownTeleportRequest x).grade = unknownTeleportGrade := rfl

@[mcfunction]
private def branchWithUnknownTeleport (condition : Val Bool) (x : Val Int32) :
    Prog (teleportGrade.join unknownTeleportGrade) Int32 :=
  Prog.branch condition
    (castGrade (teleportGrade_eq x) <|
      Command.emit (teleportRequest x))
    (castGrade (unknownTeleportGrade_eq x) <|
      Command.emit (unknownTeleportRequest x))

run_cmd
  let definition := (← elaborate ``branchWithUnknownTeleport).definition
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link definition
    | throwError "branched teleport failed object linking"
  let .ok commands := commandCatalog
    | throwError "failed to build the command catalog"
  match commands.link objectLinked with
  | .error (.unknownCommand key) =>
      unless key == `proof.unknown_teleport do
        throwError "branched unknown-route diagnostic carried the wrong key"
  | .error diagnostic =>
      throwError "expected branched unknown-route diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "unknown command nested in a Tree branch unexpectedly linked"

private def fakeTeleportSig : Command.Signature :=
  { Std.Command.Declarations.teleport.signature with eff := Eff.none }

private def fakeTeleportRequest (x : Val Int32) :
    Command.Call EncodedVal fakeTeleportSig :=
  { ref := ⟨Std.Command.Declarations.teleport.key, Std.Command.Declarations.teleport.template, none⟩
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
  let definition := (← elaborate ``fakeTeleport).definition
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link definition
    | throwError "fake teleport failed object linking"
  let .ok commands := commandCatalog
    | throwError "failed to build the command catalog"
  match commands.link objectLinked with
  | .error (.commandSignatureMismatch key) =>
      unless key == Std.Command.Declarations.teleport.key do
        throwError "route-signature diagnostic carried the wrong key"
  | .error diagnostic =>
      throwError "expected route-signature diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "route-signature mismatch unexpectedly linked"

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

private theorem swappedTemplateGrade_eq (x : Val Int32) :
    (swappedTemplateRequest x).grade = swappedTemplateGrade := rfl

@[mcfunction]
private def swappedTemplate (x : Val Int32) :
    Prog swappedTemplateGrade Int32 :=
  castGrade (swappedTemplateGrade_eq x) <|
    Command.emit (swappedTemplateRequest x)

run_cmd
  let definition := (← elaborate ``swappedTemplate).definition
  let .ok objects := ObjectCatalog.build []
    | throwError "failed to build the primitive object catalog"
  let .ok objectLinked := objects.link definition
    | throwError "swapped template failed object linking"
  let .ok commands := commandCatalog
    | throwError "failed to build the command catalog"
  match commands.link objectLinked with
  | .error (.commandTemplateMismatch key) =>
      unless key == Std.Command.Declarations.teleport.key do
        throwError "template diagnostic carried the wrong key"
  | .error diagnostic =>
      throwError "expected template diagnostic, got {repr diagnostic}"
  | .ok _ => throwError "command template mismatch unexpectedly linked"

end Oria.Proofs.TreeCommandCatalog
