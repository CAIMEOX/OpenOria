module

import Oria
import Oria.Compiler.Definition
import Oria.Proofs.Fixtures.Envelope
import Oria.Proofs.McFunctionUtil
meta import Oria
meta import Oria.Compiler.Definition
meta import Oria.Proofs.Fixtures.Envelope
meta import Oria.Proofs.McFunctionUtil

namespace Oria.Proofs.Pattern

open Oria Oria.IR Lean Lean.Elab.Command
open Oria.Proofs.Fixtures Oria.Proofs.McFunctionUtil

private def lowerPattern (name : Lean.Name) : CommandElabM Unit := do
  let elaborated ← elaborate name
  let .ok objects := ObjectCatalog.build [MaybeI32.Oria.schema]
    | throwError "pattern object catalog failed"
  let .ok objectLinked := objects.link elaborated.definition
    | throwError "object linking failed"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "command catalog failed"
  let .ok commandLinked := commands.link objectLinked
    | throwError "command linking failed"
  let .ok functions := Function.Catalog.build []
    | throwError "function catalog failed"
  let .ok linked := functions.link commandLinked
    | throwError "function linking failed"
  let .ok _ := Oria.Lower.ANF.lower elaborated.source linked
    | throwError "ANF lowering failed"
  pure ()

@[mcfunction]
private def incomplete (value : Val MaybeI32) : Prog .pure Int32 := do
  match value with
  | .none => return 0

run_cmd
  let elaborated ← elaborate ``incomplete
  let .ok objects := ObjectCatalog.build [MaybeI32.Oria.schema]
    | throwError "object catalog failed"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "command catalog failed"
  let .ok functions := Function.Catalog.build []
    | throwError "function catalog failed"
  match Compiler.compile functions objects commands elaborated with
  | .error (.nonExhaustiveMatch name) =>
      unless name == elaborated.source do throwError "match diagnostic named another function"
  | .error diagnostic => throwError "unexpected pattern diagnostic: {repr diagnostic}"
  | .ok _ => throwError "incomplete pattern matrix compiled"

@[mcfunction]
private def reordered (value : Val MaybeI32) : Prog .pure Int32 := do
  match value with
  | .some x => return x
  | .none => return 0

run_cmd
  lowerPattern ``reordered

example (choice : Val Choice) : Prog .pure Int32 := do
  match choice with
  | .rock => return 0
  | .paper => return 1
  | .scissors => return 2

example (envelope : Val Envelope) : Prog .pure Int32 := do
  match envelope with
  | .wrap .none => return 0
  | .wrap (.some x) => return x

example (value : Val TwoPayload) : Prog .pure Int32 := do
  match value with
  | .left x => return x
  | .right x => return x

end Oria.Proofs.Pattern
