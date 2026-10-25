module

public import Oria.IR.DP121.Program
import Oria.IR.DP121.Transform
import Oria.IR.DP121.Pretty
import Std.Data.HashMap.Basic

namespace Oria.Optimize.Sharing

open Oria.Datapack Oria.Target.DP121

private abbrev Definition := (kind : FunctionKind) × FunctionDef kind
private abbrev Alias := Std.HashMap String FunctionId

/-- Public entries and tag dispatchers retain their externally referenced resource identities. -/
private def shareable (id : FunctionId) : Bool :=
  decide id.path.Internal && id.path.val != "__oria/load" && id.path.val != "__oria/tick"

private def rename (aliases : Alias) {k : FunctionKind} (ref : FunctionRef k) : FunctionRef k :=
  .ofId (aliases.getD ref.id.render ref.id)

/- The existing DP121 renderer supplies exact command bytes. Schema equality remains an
   independent condition: identical $(p0) text can have different typed field contracts.
   Calls are rewritten in the structured IR, never by replacing text in rendered commands. -/
private def step (definitions : Array Definition) : Array Definition := Id.run do
  let mut known : Std.HashMap String (List (FunctionKind × FunctionId)) := {}
  let mut aliases : Alias := {}
  for ⟨kind, definition⟩ in definitions do
    if shareable definition.ref.id then
      let key := definition.body.pretty 120
      let candidates := known.getD key []
      match candidates.find? (fun (other, _) => decide (kind = other)) with
      | some (_, representative) =>
          aliases := aliases.insert definition.ref.id.render representative
      | none => known := known.insert key ((kind, definition.ref.id) :: candidates)
  return definitions.filterMap fun ⟨kind, definition⟩ =>
    if aliases.contains definition.ref.id.render then none
    else some ⟨kind, { definition with body := definition.body.mapFunctions (rename aliases) }⟩

/-- Intern private definitions by exact emitted body and call kind. Revisit callers after
renaming exposes further sharing; each nonterminal round strictly reduces the file count. -/
public def run (definitions : Array ((kind : FunctionKind) × FunctionDef kind)) :
    Array ((kind : FunctionKind) × FunctionDef kind) :=
  let next := step definitions
  if _h : next.size < definitions.size then run next else next
termination_by definitions.size

end Oria.Optimize.Sharing
