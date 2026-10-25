module

public import Oria.IR.DP121.Program
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

namespace Oria.Optimize.Linearize

open Oria.Target.DP121

private abbrev Definition := (kind : FunctionKind) × FunctionDef kind
private abbrev Commands := Array (Command .plain)

private def flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

/-- A tail call can share its caller's return destination. A conditional successor
becomes fallthrough behind an inverted guard for the other edge. -/
private def splice (lookup : FunctionRef .plain → Option Commands) (commands : Commands) :
    Option (String × Commands) := do
  let .returnRun (.function no) :: rest := commands.toList.reverse | none
  if let .when polarity condition (.returnRun (.function yes)) :: before := rest then
    if let some body := lookup yes then
      return (yes.id.render, before.reverse.toArray ++
        #[.when (flip polarity) condition (.returnRun (.function no))] ++ body)
  if let some body := lookup no then
    return (no.id.render, rest.reverse.toArray ++ body)
  none

private def step (definitions : Array Definition) : Array Definition := Id.run do
  let mut uses : Std.HashMap String Nat := {}
  let mut bodies : Std.HashMap String Commands := {}
  for ⟨_, definition⟩ in definitions do
    for (_, name) in definition.body.calls do
      uses := uses.insert name (uses.getD name 0 + 1)
    if let .plain commands := definition.body then
      bodies := bodies.insert definition.ref.id.render commands
  let mut removed : Std.HashSet String := {}
  let mut changed : Std.HashSet String := {}
  let mut result := #[]
  for definition in definitions do
    let ⟨kind, value⟩ := definition
    let parent := value.ref.id.render
    if removed.contains parent then continue
    match kind, value with
    | .plain, value =>
      let lookup (ref : FunctionRef .plain) : Option Commands := do
        let name := ref.id.render
        guard (decide ref.id.path.Internal && name != parent && uses.getD name 0 == 1 &&
          ref.id.path.val != "__oria/load" && ref.id.path.val != "__oria/tick" &&
          !removed.contains name && !changed.contains name)
        let body ← bodies[name]?
        match body.back? with
        | some (.returnValue _) | some .returnFail | some (.returnRun _) => some body
        | _ => none
      let .plain commands := value.body
      if let some (child, commands) := splice lookup commands then
        removed := removed.insert child
        changed := changed.insert parent
        result := result.push ⟨.plain, { value with body := .plain commands }⟩
      else result := result.push definition
    | .macro _, _ => result := result.push definition
  return result.filter fun ⟨_, definition⟩ => !removed.contains definition.ref.id.render

/-- Splice uniquely referenced, explicitly returning private plain successors without duplicating bodies.
Scheduled and macro/Execute references participate in use counts. Each changing round
removes a definition; public identities and shared or cyclic destinations remain addressable. -/
public def run (definitions : Array ((kind : FunctionKind) × FunctionDef kind)) :
    Array ((kind : FunctionKind) × FunctionDef kind) :=
  let next := step definitions
  if _h : next.size < definitions.size then run next else next
termination_by definitions.size

end Oria.Optimize.Linearize
