module

import Oria.Command
import Oria.Proofs.McFunctionUtil
meta import Oria.Command
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Meta.Elab.ProgDo

namespace Oria.Proofs.OpenCodec

open Oria
open Lean Lean.Elab Command
open Oria.Proofs.McFunctionUtil

private def tokenRejected (text : String) : Bool :=
  match Command.SyntaxToken.parse text with
  | .error _ => true
  | .ok _ => false

#guard tokenRejected "two words"
#guard tokenRejected "$(untracked)"
#guard tokenRejected "\"unterminated"
#guard tokenRejected "\\escape"
#guard tokenRejected "\u0000"
#guard tokenRejected "\u007f"

/-- A downstream argument type: extending command arguments must not edit compiler syntax. -/
private inductive PairArg where
  | pair : Val Int32 → Val Int32 → PairArg

private def pairKey : Command.SlotKey :=
  ⟨`proof.pair.argument⟩

private instance : Command.ArgCodec PairArg where
  key := pairKey
  encode
    | .pair left right =>
        Command.Fragment.spaced [
          Command.Fragment.hole .i32 left,
          Command.Fragment.hole .i32 right
        ]

example (left right : Val Int32) :
    (Command.encode (PairArg.pair left right)).holeCount = 2 := rfl

private def pairSig : Command.Signature :=
  { schema := [pairKey]
    req := Req.none
    eff := Eff.none }

private def pairKeyword : Command.SyntaxToken :=
  .ofString "pair"

example : Command.SyntaxToken.Valid pairKeyword.text :=
  pairKeyword.valid

private def pairTemplate : Command.Template [pairKey] :=
  { parts := [.token pairKeyword, .space, .slot ⟨0, by simp⟩] }

private def pair : Command.Ref pairSig :=
  ⟨`proof.pair, pairTemplate, none⟩

example : Command.Decl :=
  pair.declaration

example (argument : PairArg) :
    Prog (pair.call (.cons (Command.encode argument) .nil)).grade Int32 :=
  Command.emit <| pair.call (.cons (Command.encode argument) .nil)

@[mcfunction]
private def pairDefinition (left right : Val Int32) :
    Prog pairSig.grade Int32 := do
  Command.emit <| pair.call (.cons (Command.encode (PairArg.pair left right)) .nil)

run_cmd
  let elaborated ← elaborate ``pairDefinition
  unless elaborated.signature == pairDefinition.signature do
    throwError "open codec elaborated with the wrong signature"
  let commands ←
    match Command.Catalog.build [pair.declaration] with
    | .ok commands => pure commands
    | .error diagnostic => throwError "failed to build command catalog: {repr diagnostic}"
  let objects ←
    match ObjectCatalog.build [] with
    | .ok objects => pure objects
    | .error diagnostic => throwError "failed to build object catalog: {repr diagnostic}"
  let objectLinked ←
    match objects.link elaborated.definition with
    | .ok linked => pure linked
    | .error diagnostic => throwError "failed to link open codec objects: {repr diagnostic}"
  unless (commands.link objectLinked).isOk do
    throwError "failed to link open codec command"

end Oria.Proofs.OpenCodec
