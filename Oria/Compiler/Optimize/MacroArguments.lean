module

public import Oria.IR.DP121.Program
import Oria.Compiler.Lower.DP121.Stack
import Std.Data.HashSet.Basic

namespace Oria.Optimize.MacroArguments

open Oria.Target.DP121 Oria.Lower.DP121

private abbrev Definition := (kind : FunctionKind) × FunctionDef kind
private abbrev Cache := List (StoragePath × Transfer.Source Place)
private abbrev Known := Std.HashSet String

private def root (path : StoragePath) : Option String :=
  match path.path.head with | .key key => some key.text | _ => none

private def separate (a b : StoragePath) : Bool :=
  a.storage != b.storage || match root a, root b with
    | some x, some y => x != y
    | _, _ => false

private def parameter (storage : ResourceId) (path : StoragePath) : Bool :=
  path.storage == storage && root path == some "macro" &&
    match path.path.tail with | [.key _] => true | _ => false

private def temporary (storage : ResourceId) (path : StoragePath) : Bool :=
  path.storage == storage && match root path with
    | some name => name == "macro" || name == "stack"
    | none => true

private def base {m : Mode} : DataPath m → StoragePath
  | .static path | .index path .. | .key path .. => path

private def preservesData {m : Mode} (storage : ResourceId) : DataCommand m → Bool
  | .get _ => true
  | .setValue p _ | .setFrom p _ | .appendFrom p _ | .remove p => !temporary storage (base p)

private def preserves {m : Mode} (storage : ResourceId) (known : Known) : Command m → Bool
  | .scoreboard (.get _) => true
  | .scoreboard _ => false
  | .data op => preservesData storage op
  | .native value => value.temporaries == .preserves
  | .function ref | .functionWithStorage ref _ => known.contains ref.id.render
  | .when _ _ inner | .returnRun inner => preserves storage known inner
  | .store _ (.storageI32 path) inner =>
      !temporary storage path && preserves storage known inner
  | .returnValue _ | .returnFail => true
  | _ => false

private def preservesBody {k : FunctionKind} (storage : ResourceId) (known : Known) :
    FunctionBody k → Bool
  | .plain commands => commands.all (preserves storage known)
  | .macro lines => lines.all fun
      | .static command => preserves storage known command
      | .macro line => preserves storage known line.command

private def summaries (storage : ResourceId) (definitions : Array Definition) : Known := Id.run do
  let mut known : Known := {}
  let mut changed := true
  while changed do
    let old := known.size
    for ⟨_, d⟩ in definitions do
      if preservesBody storage known d.body then known := known.insert d.ref.id.render
    changed := old != known.size
  return known

private def score (target : Score) (cache : Cache) : Cache :=
  cache.filter fun (_, value) => value != .loc (.score target)

private def write (storage : ResourceId) (target : StoragePath) (cache : Cache) : Cache :=
  cache.filter fun (path, value) =>
    (if parameter storage target then path != target else separate path target) &&
      match value with
      | .loc (.storage source) => separate source target
      | _ => true

private def touch (storage : ResourceId) (known : Known) (cache : Cache) : Command .plain → Cache
  | .scoreboard (.get _) => cache
  | .scoreboard (.set target _) | .scoreboard (.add target ..) | .scoreboard (.remove target ..) =>
      score target cache
  | .scoreboard (.operation target op source) =>
      let cache := score target cache
      if op == .swap then score source cache else cache
  | .scoreboard (.objectiveAdd _) => []
  | .data (.get _) => cache
  | .data (.setValue (.static p) _) | .data (.setFrom (.static p) _) |
      .data (.appendFrom (.static p) _) | .data (.remove (.static p)) => write storage p cache
  | .when _ _ (.returnRun _) | .when _ _ (.returnValue _) | .when _ _ .returnFail => cache
  | .when _ _ inner | .returnRun inner => touch storage known cache inner
  | .store _ (.score target) inner => score target (touch storage known cache inner)
  | .store _ (.storageI32 target) inner => write storage target (touch storage known cache inner)
  | command => if preserves storage known command then cache else []

/-- Only compiler-owned scalar argument stores are candidates. Native NBT arguments
retain their copy semantics; frame sources are invalidated by every stack mutation. -/
private def preparation (storage : ResourceId) : Command .plain → Option (StoragePath × Transfer.Source Place)
  | .store .result (.storageI32 target) (.scoreboard (.get source)) =>
      if parameter storage target then some (target, .loc (.score source)) else none
  | .data (.setValue (.static target) (.int value)) =>
      if parameter storage target then some (target, .imm value) else none
  | .data (.setFrom (.static target) (.static source)) =>
      if parameter storage target && source.storage == storage && root source == some "stack" then
        some (target, .loc (.storage source))
      else none
  | _ => none

private def rewrite (storage : ResourceId) (known : Known) (commands : Array (Command .plain)) :
    Array (Command .plain) := Id.run do
  let mut cache : Cache := []
  let mut result := #[]
  for (command, i) in commands.zipIdx do
    if let some entry := preparation storage command then
      if cache.contains entry && i + 1 < commands.size then continue
      cache := entry :: touch storage known cache command
    else cache := touch storage known cache command
    result := result.push command
  return result

/-- Reuse prepared scalar fields within each linearized target function. Lowering supplies
native temporary effects; unknown calls, source writes, stack changes, and macro overwrites
invalidate facts. Capture destinations remain ordinary writes, including on failure. -/
public def run (storage : ResourceId)
    (definitions : Array ((kind : FunctionKind) × FunctionDef kind)) :
    Array ((kind : FunctionKind) × FunctionDef kind) :=
  let known := summaries storage definitions
  definitions.map fun ⟨kind, d⟩ =>
    match kind, d.body with
    | .plain, .plain commands => ⟨.plain, {d with body := .plain (rewrite storage known commands)}⟩
    | .macro schema, _ => ⟨.macro schema, d⟩

end Oria.Optimize.MacroArguments
