module

public import Oria.Compiler.Lower.DP121.Persistent.Runtime
public import Oria.IR.Representation.Persistent
public import Oria.IR.Common.Json
import Lean.Data.Json.Printer

namespace Oria.Lower.DP121.Persistent.Initialize

open Oria Oria.Target.DP121

/-- A closed initializer which publishes its complete root word vector before returning. -/
public structure Root where
  entry : FunctionRef .plain

/-- Stable root/schema identity excludes transient plan IDs and initializer code. -/
public def manifest (table : Representation.Table) (roots : Array (ResourceId × ObjTy)) :
    Except Diagnostic String := do
  let roots := roots.qsort fun a b => a.1.text < b.1.text
  let types ← Representation.Persistent.reachableTypes table (roots.map (·.2))
  let schemas := types.toList.filterMap fun type =>
    match type with
    | .data id => table.schema? id
    | _ => none
  let schemas := (schemas.map Lean.toJson).toArray.qsort fun a b => a.compress < b.compress
  let words (type : ObjTy) := ((table.kinds type).toList.map fun word =>
      match word with
      | .scalar => Lean.Json.str "scalar"
      | .pointer type => Lean.Json.mkObj [("pointer", Lean.toJson type)]).toArray
  let layouts := (types.map fun type => Lean.Json.mkObj
    [("type", Lean.toJson type), ("words", .arr (words type))]).qsort
      (fun a b => a.compress < b.compress)
  let roots := roots.map fun (id, type) =>
    Lean.Json.mkObj [("id", .str id.text), ("type", Lean.toJson type),
      ("words", .arr (words type))]
  pure (Lean.Json.mkObj [("roots", .arr roots), ("types", .arr schemas),
    ("layouts", .arr layouts)]).compress

/-- Initialize fresh state or validate an existing heap before publishing readiness. -/
public def generate (config : Oria.Runtime.Config) (schema : String) (roots : Array Root) :
    Except Diagnostic (List ((kind : FunctionKind) × FunctionDef kind)) := do
  let load ← Runtime.ref config "load"
  let fresh ← Runtime.ref config "fresh"
  let check ← Runtime.ref config "check"
  let ready := Runtime.score config "#ready"
  let panic := Runtime.score config "#panic"
  let present := Runtime.score config "#persistent_exists"
  let version := Runtime.score config "#persistent_abi"
  let different := Runtime.score config "#schema_changed"
  let path (key : String) : StoragePath := ⟨config.storage, .key key⟩
  let scratch : StoragePath := ⟨config.runtime, .key "schema_check"⟩
  let failed (condition : ScoreCondition) : List (Command .plain) := [
    Command.when .negative condition (.scoreboard (.set panic 1)),
    .when .negative condition .returnFail ]
  let loadCommands : List (Command .plain) := [
    .scoreboard (.set ready 0),
    .scoreboard (.set panic 0),
    .store .success (.score present) (.data (.get (path "abi"))),
    .when .negative (.matches present (.exact 1)) (.returnRun (.function fresh)),
    .returnRun (.function check) ]
  let heap : Heap.Config := ⟨config.runtime, config.objective⟩
  let initialized := Runtime.score config "#initialized"
  let initializers := roots.toList.flatMap fun root =>
    Heap.begin heap ++ [.store .success (.score initialized) (.function root.entry)] ++
    Heap.finish heap ++ [
      .when .positive (.matches panic (.exact 1)) .returnFail,
      .when .negative (.matches initialized (.exact 1)) .returnFail ]
  let freshCommands : List (Command .plain) := [
    .data (.setValue (path "slots") (.list (.nil : Nbt.Values))),
    .data (.setValue (path "roots") (.compound .nil)),
    .data (.setValue (path "epoch") (.int 0)),
    .data (.setValue (path "used") (.int 0)),
    .data (.setValue (path "free") (.int 0)) ] ++ initializers ++ [
    .data (.setValue (path "schema") (.string schema)),
    .data (.setValue (path "abi") (.int 2)),
    .scoreboard (.set ready 1), .returnValue 0 ]
  let checkCommands : List (Command .plain) := [
    .store .result (.score version) (.data (.get (path "abi"))) ] ++
    failed (.matches version (.exact 2)) ++ [
    .store .success (.score present) (.data (.get (path "schema"))) ] ++
    failed (.matches present (.exact 1)) ++ [
    .data (.setFrom scratch (path "schema")),
    .store .success (.score different) (.data (.setValue scratch (.string schema))),
    .data (.remove scratch) ] ++ failed (.matches different (.exact 0)) ++ [
    .scoreboard (.set ready 1), .returnValue 0 ]
  pure [⟨.plain, ⟨load, .plain loadCommands.toArray⟩⟩,
    ⟨.plain, ⟨fresh, .plain freshCommands.toArray⟩⟩,
    ⟨.plain, ⟨check, .plain checkCommands.toArray⟩⟩]

end Oria.Lower.DP121.Persistent.Initialize
