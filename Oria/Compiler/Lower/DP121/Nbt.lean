module

public import Oria.Compiler.Lower.DP121.Command
public import Oria.Compiler.Lower.DP121.Memory
public import Oria.IR.Common.Nbt
import Oria.Nbt.Syntax

namespace Oria.Lower.DP121.Nbt

open Oria.IR Oria.Target.DP121

private abbrev Operand := Transfer.Source Place
private abbrev Fragment := Oria.Command.Fragment (fun _ => Operand)
private abbrev StaticFragment := Oria.Command.Fragment (fun _ => Empty)

private def score (config : Config) (name : Oria.Command.SyntaxToken) : Score :=
  ⟨.ofToken name, config.objective⟩

private def location (storage : ResourceId) (key : String) : StoragePath :=
  ⟨storage, .key key⟩

private def tokens {v : ObjTy → Type} (xs : List Oria.Command.SyntaxToken) : Oria.Command.Fragment v :=
  .spaced (xs.map .token)

private def atStorage {v : ObjTy → Type} (path : StoragePath) : Oria.Command.Fragment v :=
  .spaced [.token "storage", .token (.ofResourceId path.storage),
    ⟨[.literal (.path path.path)], Req.none⟩]

private def captureSuccess (flag : Score) (emitted : Emitted) : Emitted :=
  match emitted.commands.reverse with
  | [] => emitted
  | command :: before => { emitted with commands :=
      before.reverse ++ [.scoreboard (.set flag 0), .store .success (.score flag) command] }

private def requireSuccess (flag : Score) : Command .plain :=
  .when .negative (.matches flag (.exact 1)) .returnFail

private def append (left right : Emitted) : Emitted :=
  ⟨left.commands ++ right.commands, left.helpers ++ right.helpers⟩

private def checked (flag : Score) (emitted : Emitted) : Emitted :=
  let emitted := captureSuccess flag emitted
  { emitted with commands := emitted.commands ++ [requireSuccess flag] }

private def resolve {as : List ObjTy} (values : Args (fun _ => Operand) as)
    (fragment : IR.Nbt.Fragment as) : Fragment :=
  fragment.map (fun x => x.lookup values)

/-- Render semantic fields and indices only at the target encoding seam. -/
private def selection {as : List ObjTy} (values : Args (fun _ => Operand) as)
    (path : IR.Nbt.Path (Scope.Var Unit as .i32)) : Fragment :=
  path.segments.foldl (init := .empty) fun out segment =>
    out.append (match segment with
      | .key key => ⟨[.token ".", .literal (.path (.key key.text))], Req.none⟩
      | .index index => .append (.token "[")
          (.append (.hole .i32 (index.lookup values)) (.token "]"))
      | .all => .token "[]"
      | .matching impossible => nomatch impossible)

private def snapshotSource {k : Nat} (config : Config) (bank : Layout k)
    (name : String) (pointer : Operand) (path : Option Fragment) :
    Except Diagnostic (Emitted × Fragment × Option Fragment × Fragment) := do
  let input := location (← config.runtime) "nbt_input"
  let load ← Memory.project config bank (name ++ "/input") pointer
    [([.key ⟨"value"⟩], .storage input)] .either
  let load := { load with commands := [.data (.remove input)] ++ load.commands }
  let target := atStorage input
  pure (load, target, path, target.append (path.getD .empty))

private def source {as : List ObjTy} {k : Nat} (config : Config) (bank : Layout k)
    (name : String) (values : Args (fun _ => Operand) as) (value : IR.Nbt.Source as) :
    Except Diagnostic (Emitted × Fragment × Option Fragment × Fragment) := do
  match value with
  | .external target path =>
      let target := resolve values target
      let path := path.map (resolve values)
      pure (⟨[], []⟩, target, path, .spaced (target :: path.toList))
  | .value pointer path =>
      snapshotSource config bank name (pointer.lookup values) (path.map (resolve values))
  | .reference (.arena pointer) path =>
      snapshotSource config bank name (pointer.lookup values) (some (selection values path))
  | .reference (.global ref) path =>
      let target := atStorage (← config.global ref)
      let path := selection values path
      pure (⟨[], []⟩, target, some path, target.append path)

private def publish (config : Config) (storage : ResourceId) (flag result : Score) : List (Command .plain) :=
  match Heap.publish ⟨storage, config.objective⟩ (.score result) with
  | [] => []
  | command :: rest =>
      [.scoreboard (.set flag 0), .store .success (.score flag) command,
        requireSuccess flag] ++ rest

private def read {as : List ObjTy} {k : Nat} (config : Config) (bank : Layout k) (name : String)
    (mode : IR.Nbt.ReadMode) (input : IR.Nbt.Source as) (values : Args (fun _ => Operand) as)
    (wanted : Bool) : Except Diagnostic Emitted := do
  let storage ← config.runtime
  let flag := score config "#nbt_ok"
  let count := score config "#nbt_count"
  let result := score config "#nbt_result"
  let draft := location storage "draft"
  let output : StoragePath := ⟨storage, (Oria.Nbt.Path.key "draft").field "value"⟩
  let (before, target, path, selected) ← source config bank name values input
  let initial : Oria.Nbt.Value .compound := match mode with
    | .one => nbt% {tag: 0, payload: []}
    | .all => nbt% {tag: 0, payload: [], value: []}
  let mut emitted := append before ⟨[.data (.setValue draft initial)], []⟩
  let query := Oria.Command.Fragment.spaced [tokens ["data", "get"],
    if mode == .one then selected else target]
  let available := match input with
    | .reference _ path => mode == .one && path.check == .available
    | _ => false
  if !available then
    emitted := append emitted (checked flag (← Command.fragment config bank (name ++ "/check") query))
  if mode == .all then
    match path with
    | none => emitted := append emitted ⟨[.scoreboard (.set count 1)], []⟩
    | some _ =>
        let query := .spaced [tokens ["execute", "if", "data"], selected]
        let probe ← Command.fragment config bank (name ++ "/count") query
          { result := some count } (some 1)
        emitted := append emitted (checked flag probe)
  let operation := if mode == .one then tokens ["set", "from"] else tokens ["append", "from"]
  let copy := .spaced [tokens ["data", "modify"], atStorage output, operation, selected]
  let copy := checked flag (← Command.fragment config bank (name ++ "/copy") copy)
  let copy := if mode == .all then
      { copy with commands := copy.commands.map (.when .positive (.matches count (.atLeast 1))) }
    else copy
  emitted := append emitted copy
  let finish := if wanted then publish config storage flag result ++
      [.returnRun (.scoreboard (.get result))]
    else [.returnValue 0]
  pure (append emitted ⟨finish, []⟩)

private def helper (config : Config) (name : String) (body : Emitted) : Except Diagnostic Emitted := do
  let ref ← config.function name
  pure ⟨[.function ref], ⟨.plain, ⟨ref, .plain body.commands.toArray⟩⟩ :: body.helpers⟩

private def capturedHelper {k : Nat} (config : Config) (bank : Layout k) (name : String)
    (out : Vector (Option Place) 2) (body : Emitted) :
    Except Diagnostic Emitted := do
  Command.captureAfter bank out (← helper config name body)

private def refPath {k : Nat} (config : Config) (bank : Layout k) (index : Nat)
    (pointer : Operand) (suffix : Fragment) (persistent : Bool := false) : Except Diagnostic (Emitted × Fragment) := do
  let storage ← if persistent then (·.storage) <$> config.memory else config.runtime
  let target := score config (if index == 0 then "#nbt_addr0" else "#nbt_addr1")
  let (before, pointer) := Arithmetic.operand bank.scratch[0] pointer
  let commands := before ++ [Command.scoreboard (.set target (-1)),
    .scoreboard (.operation target (if persistent then .add else .subtract) pointer)]
  let base := (atStorage ⟨storage, .key (if persistent then "slots" else "arena")⟩).append
    ((Oria.Command.Fragment.token "[").append
      ((Oria.Command.Fragment.hole .i32 (.loc (.score target))).append (.token "].value")))
  return (⟨commands, []⟩, base.append suffix)

/-- Resolve the address source retained by the typed operation. Named storage needs no pointer decode. -/
private def address {as : List ObjTy} {k : Nat} (config : Config) (bank : Layout k) (index : Nat)
    (values : Args (fun _ => Operand) as) (base : IR.Nbt.Base as)
    (suffix : IR.Nbt.Path (Scope.Var Unit as .i32)) : Except Diagnostic (Emitted × Fragment) :=
  match base with
  | .arena root => refPath config bank index (root.lookup values) (selection values suffix)
  | .global ref => return (⟨[], []⟩, (atStorage (← config.global ref)).append (selection values suffix))

/-- Native source clauses retain the operand's physical home. Allocated registers are
initialized I32 scores; the fixed score provider reads them without staging an IntTag. -/
private def setValue (value : IR.Nbt.Write Operand) : Except Diagnostic StaticFragment := do
  match value with
  | .literal value =>
      value.2.checkSnbt.mapError (fun error => .invalidCommandNbt (reprStr error))
      return .spaced [tokens ["value"], .nbt value.2]
  | .i32 (.imm value) => return .spaced [tokens ["value"], .nbt (.int value)]
  | .i32 (.loc (.storage source)) => return .spaced [tokens ["from"], atStorage source]
  | .i32 (.loc (.score source)) =>
      let provider := nbt% {type: "minecraft:score",
        target: {type: "minecraft:fixed", name: $(source.holder.token.text)},
        score: $(source.objective.token.text)}
      return .spaced [tokens ["compute", "default", "integer"], .nbt provider]

/-- Native NBT operations retain the ordinary scalar-word call and result convention. -/
public def emit {as : List ObjTy} {a : ObjTy} {k : Nat} (config : Config) (bank : Layout k)
    (name : String) (op : IR.Nbt.Op as a) (values : Args (fun _ => Transfer.Source Place) as)
    (out : Vector (Option Place) op.width) : Except Diagnostic Emitted := do
  let storage ← config.runtime
  let flag := score config "#nbt_ok"
  let result := score config "#nbt_result"
  match op, values with
  | .newRef _ value, .nil =>
      value.2.checkSnbt.mapError (fun error => .invalidCommandNbt (reprStr error))
      let body : Emitted := ⟨[
        .data (.remove (location storage "draft")),
        .store .success (.score flag)
          (.data (.setValue (location storage "draft") (nbt% {tag: 0, payload: [], value: $(value)}))),
        requireSuccess flag] ++ publish config storage flag result ++
        [.returnRun (.scoreboard (.get result))], []⟩
      Command.capture bank out (← helper config name body)
  | .inspectRef root suffix numeric, values =>
      let (address, selected) ← address config bank 0 values root suffix
      let query := .spaced ([tokens ["data", "get"], selected] ++ if numeric then [.i32 1] else [])
      let command ← Command.fragment config bank name query (temporaries := .preserves)
      Command.capture bank out (append address command)
  | .inspectValue root suffix numeric, values =>
      let pointer := root.lookup values
      let (loaded, original) := Arithmetic.operand bank.scratch[0] pointer
      let positive := score config "#nbt_space"
      let mut functions := []
      let mut refs := []
      for persistent in [true, false] do
        let tag := if persistent then "persistent" else "ephemeral"
        let (address, selected) ← refPath config bank 0 pointer (resolve values suffix) persistent
        let query := .spaced ([tokens ["data", "get"], selected] ++ if numeric then [.i32 1] else [])
        let command ← Command.fragment config bank (name ++ "/" ++ tag ++ "/query") query
        let last :: rest := command.commands.reverse | throw (.unsupportedMachineLowering .anonymous)
        let f ← config.function (name ++ "/" ++ tag)
        functions := functions ++ [⟨.plain, ⟨f, .plain
          (address.commands ++ rest.reverse ++ [Command.returnRun last]).toArray⟩⟩] ++ command.helpers
        refs := refs ++ [f]
      let [p, e] := refs | throw (.unsupportedMachineLowering .anonymous)
      let body : Emitted := ⟨loaded ++ [
        .scoreboard (.set positive 0),
        .when .positive (.matches original (.atLeast 1)) (.scoreboard (.set positive 1)),
        .when .positive (.matches positive (.exact 1)) (.returnRun (.function p)),
        .returnRun (.function e)], functions⟩
      capturedHelper config bank name out body
  | .putRef root suffix value isAppend, values =>
      let (address, selected) ← address config bank 0 values root suffix
      let value ← setValue (value.map (fun x => x.lookup values))
      let operation := if isAppend then tokens ["append"] else tokens ["set"]
      let emitted ← Command.fragment config bank name
        (.spaced [tokens ["data", "modify"], selected, operation, value.map Empty.elim])
        (temporaries := .preserves)
      Command.captureAfter bank #v[out[0]'(by simp [IR.Nbt.Op.width]), none] (append address emitted)
  | .clearRef root suffix, values =>
      let (address, selected) ← address config bank 0 values root suffix
      let emitted ← Command.fragment config bank name
        (.spaced [tokens ["data", "modify"], selected, tokens ["set", "value"], .nbt (nbt% [])])
        (temporaries := .preserves)
      Command.captureAfter bank #v[out[0]'(by simp [IR.Nbt.Op.width]), none] (append address emitted)
  | .copyRef dst p src q isAppend, values =>
      let (dstAddress, target) ← address config bank 0 values dst p
      let (srcAddress, source) ← address config bank 1 values src q
      let operation := if isAppend then tokens ["append", "from"] else tokens ["set", "from"]
      let write ← Command.fragment config bank name
        (.spaced [tokens ["data", "modify"], target, operation, source])
        (temporaries := .preserves)
      Command.captureAfter bank #v[out[0]'(by simp [IR.Nbt.Op.width]), none]
        (append (append dstAddress srcAddress) write)
  | .exportRef root suffix target dest, values =>
      let (address, source) ← address config bank 0 values root suffix
      let target := .spaced [resolve values target, resolve values dest]
      let write ← Command.fragment config bank name
        (.spaced [tokens ["data", "modify"], target, tokens ["set", "from"], source])
      Command.captureAfter bank #v[out[0]'(by simp [IR.Nbt.Op.width]), none] (append address write)
  | .forget, .cons value .nil =>
      pure ⟨(out[0]'(by simp [IR.Nbt.Op.width])).toList.map
        (fun target => Stack.move ⟨target, value⟩), []⟩
  | .literal value, .nil =>
      value.checkSnbt.mapError (fun error => .invalidCommandNbt (reprStr error))
      let some target := out[0]'(by simp [IR.Nbt.Op.width]) | return ⟨[], []⟩
      let initial := nbt% {tag: 0, payload: [], value: $(value)}
      let body : Emitted := ⟨[
        .data (.remove (location storage "draft")),
        .store .success (.score flag) (.data (.setValue (location storage "draft") initial)),
        requireSuccess flag] ++ publish config storage flag result ++
        [.returnRun (.scoreboard (.get result))], []⟩
      let emitted ← helper config name body
      let emitted ← Command.capture bank #v[some (.score flag), some target] emitted
      pure { emitted with commands := emitted.commands ++ [
        .when .negative (.matches flag (.exact 1))
          (.scoreboard (.set (score config "#panic") 1)), requireSuccess flag] }
  | .integer, .cons value .nil =>
      let some target := out[0] | return ⟨[], []⟩
      let initial := nbt% {tag: 0, payload: [], value: 0}
      pure ⟨[.data (.setValue (location storage "draft") initial),
        Stack.move ⟨.storage ⟨storage, (Oria.Nbt.Path.key "draft").field "value"⟩, value⟩] ++
        Heap.publish ⟨storage, config.objective⟩ target, []⟩
  | .read mode input, values =>
      let body ← read config bank name mode input values
        (out[1]'(by simp [IR.Nbt.Op.width])).isSome
      capturedHelper config bank name out body
  | .number, .cons value .nil =>
      let input := location storage "nbt_input"
      let before ← Memory.project config bank (name ++ "/input") value
        [([.key ⟨"value"⟩], .storage input)] .either
      let command ← Command.fragment config bank (name ++ "/number")
        (.spaced [tokens ["data", "get"], atStorage input, .i32 1])
      Command.capture bank out (append before command)
  | .write target path pointer, values =>
      let input := location storage "nbt_input"
      let load ← Memory.project config bank (name ++ "/input") (pointer.lookup values)
        [([.key ⟨"value"⟩], .storage input)] .either
      let command ← Command.fragment config bank (name ++ "/write")
        (.spaced [tokens ["data", "modify"], resolve values target, resolve values path,
          tokens ["set", "from"], atStorage input])
      Command.capture bank out (append load command)

end Oria.Lower.DP121.Nbt
