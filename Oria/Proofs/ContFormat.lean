module

import Oria
import Oria.IR.Cont.Pretty
import Oria.Compiler.Definition
import Oria.Proofs.McFunctionUtil
meta import Oria
meta import Oria.IR.Cont.Pretty
meta import Oria.Compiler.Definition
meta import Oria.Proofs.McFunctionUtil

namespace Oria.Proofs.ContFormat

open Oria Oria.IR Lean Lean.Elab.Command
open Oria.Proofs.McFunctionUtil

/-!
Layout assertions for the Cont formatter, kept apart from the lowering tests: they pin how the
pretty-printer breaks lines at a given width, not what the compiler produces.
-/

/-- A small constructor dispatch, which the formatter must lay out at several widths. -/
@[mcfunction]
private def dispatch (value : Val (Option Int32)) : Prog .pure Int32 := do
  match value with
  | .none => return 0
  | .some payload => return payload

private def render (width : Nat) : CommandElabM String := do
  let elaborated ← elaborate ``dispatch
  let .ok objects := ObjectCatalog.build []
    | throwError "formatter object catalog failed"
  let .ok objectLinked := objects.link elaborated.definition
    | throwError "formatter object linking failed"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "formatter command catalog failed"
  let .ok commandLinked := commands.link objectLinked
    | throwError "formatter command linking failed"
  let .ok functions := Function.Catalog.build []
    | throwError "formatter function catalog failed"
  let .ok linked := functions.link commandLinked
    | throwError "formatter function linking failed"
  let .ok lowered := Oria.Lower.ANF.lower elaborated.source linked
    | throwError "formatter ANF lowering failed"
  pure (lowered.pretty width)

-- Narrow layouts must not leave an arm body consisting only of blank space.
run_cmd do
  let narrow ← render 30
  if narrow.contains "none(\n        \n" then
    throwError "narrow Cont layout contains a spurious blank line:\n{narrow}"

-- An unbreakable line stays intact once the layout is wide enough for it.
run_cmd do
  let wide ← render 120
  let wider ← render 400
  unless wide == wider do
    throwError "Cont layout still reflows at generous widths:\nwide:\n{wide}\nwider:\n{wider}"

end Oria.Proofs.ContFormat
