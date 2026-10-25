module

import Oria.Nbt.Syntax

public import Oria.Compiler.Lower.DP121.Persistent.Runtime
public import Oria.IR.Representation.Persistent

namespace Oria.Lower.DP121.Persistent.Promote

open Oria Oria.Command Oria.Target.DP121
open Oria.Representation.Persistent

private abbrev Packed := (kind : FunctionKind) × FunctionDef kind

private def path (config : Oria.Runtime.Config) (key : String)
    (suffix : List Nbt.PathSegment := []) : StoragePath :=
  ⟨config.runtime, ⟨.key ⟨key⟩, suffix⟩⟩

private def frame (config : Oria.Runtime.Config) (suffix : List Nbt.PathSegment) : StoragePath :=
  path config "promotion" (.index (-1) :: suffix)

private def sourceScore (config : Oria.Runtime.Config) := Runtime.score config "#p_source"
private def resultScore (config : Oria.Runtime.Config) := Runtime.score config "#p_result"

private def fromScore (target : StoragePath) (source : Score) : Command .plain :=
  .store .result (.storageI32 target) (.scoreboard (.get source))

private def fromData (target : Score) (source : StoragePath) : Command .plain :=
  .store .result (.score target) (.data (.get source))

private def position : Fin Heap.addressSchema.fields.length := ⟨0, by simp [Heap.addressSchema]⟩

private def sourceAddress (config : Oria.Runtime.Config) : List (Command .plain) :=
  let index := Runtime.score config "#promote_index"
  [ .scoreboard (.set index (-1))
  , .scoreboard (.operation index .subtract (sourceScore config))
  , fromScore (path config "memory_arg" [.key (Heap.addressSchema.parameterKey position)]) index ]

private def macroRef (config : Oria.Runtime.Config) (name : String) :
    Except Diagnostic (FunctionRef (.macro Heap.addressSchema)) := do
  let ref ← Runtime.ref config name
  pure (.ofId ref.id)

private def plain (config : Oria.Runtime.Config) (name : String) (commands : List (Command .plain)) :
    Except Diagnostic Packed := do
  pure ⟨.plain, ⟨← Runtime.ref config name, .plain commands.toArray⟩⟩

private def macroLine (command : Command (.macro Heap.addressSchema))
    (used : 0 < command.parameterCount) : FunctionLine Heap.addressSchema :=
  .macro (.ofCommand command used)

private def failure (config : Oria.Runtime.Config) : List (Command .plain) :=
  [.scoreboard (.set (Runtime.score config "#panic") 1), .returnFail]

private def memoSave (config : Oria.Runtime.Config) (index : Nat) : Except Diagnostic Packed := do
  let ref ← macroRef config s!"copy/{index}/memo"
  let command : Command (.macro Heap.addressSchema) :=
    .data (.setFrom (.key (path config "memo") position []) (path config "memo_entry"))
  pure ⟨.macro Heap.addressSchema, ⟨ref, .macro #[macroLine command (by
    simp [command, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount])]⟩⟩

private def copyConstructor (config : Oria.Runtime.Config) (index arm : Nat)
    {n : Nat} (plan : ConstructorPlan n) : Except Diagnostic Packed := do
  let allocate ← Runtime.ref config "allocate"
  let read ← macroRef config "read"
  let replace ← macroRef config "replace"
  let save ← macroRef config s!"copy/{index}/memo"
  let scratch := path config "promote_frame"
  let object := path config "memory_object"
  let draft := path config "memory_draft"
  let src := sourceScore config
  let dst := resultScore config
  if !plan.actions.any (fun | .copy _ => true | _ => false) then
    return ← plain config s!"copy/{index}/{arm}" <| [
      .data (.setFrom draft object),
      .data (.setValue (path config "memory_draft" [.key ⟨"d"⟩]) (.int (Int32.ofNat plan.layout.scanCode))),
      .function allocate,
      .data (.setValue (path config "memo_entry") (nbt% {dst: 0, plan: $(Int32.ofNat index)})),
      fromScore (path config "memo_entry" [.key ⟨"dst"⟩]) dst] ++
      sourceAddress config ++ [.functionWithStorage save (Runtime.source config), .returnValue 0]
  let seed := nbt% {
    d: $(Int32.ofNat plan.layout.scanCode), tag: $(plan.layout.tag),
    payload: $(Array.replicate plan.slots (0 : Int32))}
  let mut commands : List (Command .plain) := [
    .data (.setValue scratch (nbt% {src: 0, dst: 0})),
    fromScore (path config "promote_frame" [.key ⟨"src"⟩]) src,
    .data (.setFrom (path config "promote_frame" [.key ⟨"object"⟩]) object),
    .data (.appendFrom (path config "promotion") scratch),
    .data (.setValue draft seed),
    .function allocate,
    fromScore (frame config [.key ⟨"dst"⟩]) dst ]
  commands := commands ++ Runtime.address config (.inr dst) ++ [
    .functionWithStorage read (Runtime.source config),
    .data (.setFrom (frame config [.key ⟨"target"⟩]) object),
    .data (.setFrom (frame config [.key ⟨"target"⟩, .key ⟨"payload"⟩])
      (frame config [.key ⟨"object"⟩, .key ⟨"payload"⟩])),
    fromData dst (frame config [.key ⟨"dst"⟩]),
    .data (.setValue (path config "memo_entry") (nbt% {dst: 0, plan: $(Int32.ofNat index)})),
    fromScore (path config "memo_entry" [.key ⟨"dst"⟩]) dst,
    fromData src (frame config [.key ⟨"src"⟩]) ] ++
    sourceAddress config ++ [.functionWithStorage save (Runtime.source config)]
  for field in List.finRange plan.slots do
    match plan.actions[field] with
    | .scalar | .retainRef _ => pure ()
    | .copy child =>
        let call ← Runtime.ref config s!"copy/{child.val}"
        commands := commands ++ [
          fromData src (frame config [.key ⟨"object"⟩, .key ⟨"payload"⟩, .index field.val]),
          .function call,
          fromScore (frame config [.key ⟨"target"⟩, .key ⟨"payload"⟩, .index field.val]) dst ]
  if let .nbt _ := plan.layout.type then
    commands := commands ++ [
      .data (.setFrom (frame config [.key ⟨"target"⟩, .key ⟨"value"⟩])
        (frame config [.key ⟨"object"⟩, .key ⟨"value"⟩]))]
  commands := commands ++ [
    fromData dst (frame config [.key ⟨"dst"⟩]),
    .data (.setFrom draft (frame config [.key ⟨"target"⟩])) ] ++
    Runtime.address config (.inr dst) ++ [
    .functionWithStorage replace (Runtime.source config),
    fromData dst (frame config [.key ⟨"dst"⟩]),
    .data (.remove (path config "promotion" [.index (-1)])),
    .returnValue 0 ]
  plain config s!"copy/{index}/{arm}" commands

private def lookup (config : Oria.Runtime.Config) (index : Nat)
    {n : Nat} (constructors : Array (ConstructorPlan n)) : Except Diagnostic Packed := do
  let found := Runtime.score config "#promote_found"
  let plan := Runtime.score config "#promote_plan"
  let tag := Runtime.score config "#promote_tag"
  let dst := resultScore config
  let memo := path config "memo"
  let hit : ScoreCondition := .matches found (.exact 1)
  let wrong : ScoreCondition := .matches plan (.exact (Int32.ofNat index))
  let get : Command (.macro Heap.addressSchema) :=
    .store .success (.score found)
      (.store .result (.score dst) (.data (.get (.key memo position [.key ⟨"dst"⟩]))))
  let getPlan : Command (.macro Heap.addressSchema) :=
    .when .positive hit
      (.store .result (.score plan) (.data (.get (.key memo position [.key ⟨"plan"⟩]))))
  let readObject : Command (.macro Heap.addressSchema) :=
    .data (.setFrom (path config "memory_object")
      (.index ⟨config.runtime, .key "arena"⟩ position []))
  let mut lines : Array (FunctionLine Heap.addressSchema) := #[
    .static (.scoreboard (.set dst 0)),
    .static (.scoreboard (.set plan (-1))),
    macroLine get (by simp [get, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]),
    macroLine getPlan (by simp [getPlan, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]),
    .static (.when .positive hit (.when .negative wrong
      (.scoreboard (.set (Runtime.score config "#panic") 1)))),
    .static (.when .positive hit (.when .negative wrong .returnFail)),
    .static (.when .positive hit (.returnValue 0)),
    macroLine readObject (by simp [readObject, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]),
    .static (fromData tag (path config "memory_object" [.key ⟨"tag"⟩])) ]
  for arm in List.finRange constructors.size do
    let target ← Runtime.ref config s!"copy/{index}/{arm.val}"
    lines := lines.push (.static (.when .positive
      (.matches tag (.exact constructors[arm].layout.tag)) (.returnRun (.function target))))
  lines := lines ++ (failure config).toArray.map FunctionLine.static
  pure ⟨.macro Heap.addressSchema,
    ⟨← macroRef config s!"copy/{index}/lookup", .macro lines⟩⟩

/-- Per-type copy helpers retain positive pointers and memoize reserved destinations before recursion. -/
public def generate (config : Oria.Runtime.Config) (plans : PlanTable) :
    Except Diagnostic (List ((kind : FunctionKind) × FunctionDef kind)) := do
  let mut functions := []
  for index in List.finRange plans.nodeCount do
    match plans.nodes[index] with
    | .immediate _ | .ref _ _ _ => pure ()
    | .boxed _ constructors =>
        let src := sourceScore config
        let dst := resultScore config
        let positive : ScoreCondition := .matches src (.atLeast 1)
        let zero : ScoreCondition := .matches src (.exact 0)
        let target ← macroRef config s!"copy/{index.val}/lookup"
        let commands := [
          Command.when .positive positive (.scoreboard (.operation dst .assign src)),
          .when .positive positive (.returnValue 0),
          .when .positive zero (.scoreboard (.set (Runtime.score config "#panic") 1)),
          .when .positive zero .returnFail ] ++ sourceAddress config ++
          [.returnRun (.functionWithStorage target (Runtime.source config))]
        functions := functions ++ [← plain config s!"copy/{index.val}" commands,
          ← lookup config index.val constructors, ← memoSave config index.val]
        for arm in List.finRange constructors.size do
          functions := functions ++ [← copyConstructor config index.val arm.val constructors[arm]]
  pure functions

end Oria.Lower.DP121.Persistent.Promote
