module

public import Oria.Compiler.Lower.DP121.Emit
import Oria.IR.Common.Json
import Lean.Data.Json.Printer

namespace Oria.Lower.DP121.Globals

open Oria Oria.Target.DP121

/-- Native schema identity is independent of registration order and initializer contents. -/
private def manifest (globals : Array (IR.Nbt.GlobalDecl × StoragePath)) : String :=
  let roots := globals.map fun (decl, target) =>
    Lean.Json.mkObj [("storage", .str target.storage.text),
      ("path", .str (decl.ref.path.format.pretty 120)), ("schema", Lean.toJson decl.ref.schema)]
  (Lean.Json.arr (roots.qsort fun a b => a.compress < b.compress)).compress

/-- Initialize owned native subtrees before callbacks, or retain matching-schema contents.
Readiness is published after every root is available. Managed-heap initialization precedes this call. -/
public def generate (config : Config) : Except Diagnostic Emitted := do
  if config.globals.isEmpty then return ⟨[], []⟩
  let memory ← config.memory
  let load ← config.function "__oria/globals/load"
  let fresh ← config.function "__oria/globals/fresh"
  let check ← config.function "__oria/globals/check"
  let ready : Score := ⟨.ofToken "#ready", config.objective⟩
  let panic : Score := ⟨.ofToken "#panic", config.objective⟩
  let status : Score := ⟨.ofToken "#global_ok", config.objective⟩
  let schema : StoragePath := ⟨memory.storage, .key "globals"⟩
  let scratch : StoragePath := ⟨memory.runtime, .key "schema_check"⟩
  let globals ← config.globals.mapM fun decl => return (decl, ← config.global decl.ref)
  let expected := manifest globals
  let require (n : Int32) : List (Command .plain) := [
    .when .negative (.matches status (.exact n)) (.scoreboard (.set panic 1)),
    .when .negative (.matches status (.exact n)) .returnFail]
  let loadBody : List (Command .plain) := [
    .when .negative (.matches ready (.exact 1)) .returnFail,
    .scoreboard (.set panic 0),
    .scoreboard (.set ready 0),
    .store .success (.score status) (.data (.get schema)),
    .when .negative (.matches status (.exact 1)) (.returnRun (.function fresh)),
    .returnRun (.function check)]
  let seeds := globals.toList.flatMap fun (decl, target) =>
    [.data (.remove target),
      .store .success (.score status) (.data (.setValue target decl.initial.2))] ++ require 1
  let freshBody := seeds ++ [Command.data (.setValue schema (.string expected)),
    .scoreboard (.set ready 1), .returnValue 0]
  let present := globals.toList.flatMap fun (_, target) =>
    [.store .success (.score status) (.data (.get target))] ++ require 1
  let checkBody := [Command.data (.setFrom scratch schema),
    .store .success (.score status) (.data (.setValue scratch (.string expected))),
    .data (.remove scratch)] ++ require 0 ++ present ++ [
    .scoreboard (.set ready 1), .returnValue 0]
  return ⟨[.function load], [⟨.plain, ⟨load, .plain loadBody.toArray⟩⟩,
    ⟨.plain, ⟨fresh, .plain freshBody.toArray⟩⟩, ⟨.plain, ⟨check, .plain checkBody.toArray⟩⟩]⟩

end Oria.Lower.DP121.Globals
