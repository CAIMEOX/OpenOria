module

public import Oria.Compiler.Lower.DP121.Heap
public import Oria.Runtime.Config
import Oria.Nbt.Syntax

namespace Oria.Lower.DP121.Persistent.Runtime

open Oria Oria.Command Oria.Datapack Oria.Target.DP121 Nbt
open Oria.Runtime (Config)

/-- Build a scoreboard location in the runtime objective. -/
public def score (config : Config) (token : SyntaxToken) : Score :=
  ⟨ScoreHolder.ofToken token, config.objective⟩

private def pResult (config : Config) : Score := score config "#p_result"
private def pFree (config : Config) : Score := score config "#p_free"
private def pUsed (config : Config) : Score := score config "#p_used"
private def pEpoch (config : Config) : Score := score config "#p_epoch"
private def pIndex (config : Config) : Score := score config "#p_index"
private def pNext (config : Config) : Score := score config "#p_next"
private def pOk (config : Config) : Score := score config "#p_ok"
private def oneScore (config : Config) : Score := score config "#p_one"
private def panic (config : Config) : Score := score config "#panic"
private def persistentPath (config : Config) (key : String) : StoragePath :=
  ⟨config.storage, Nbt.Path.key key⟩

private def runtimePath (config : Config) (key : String) : StoragePath :=
  ⟨config.runtime, Nbt.Path.key key⟩

private def childKey (path : StoragePath) (key : String) : StoragePath :=
  { path with path := path.path.child (.key ⟨key⟩) }

private def slotsPath (config : Config) : StoragePath :=
  persistentPath config "slots"

private def usedPath (config : Config) : StoragePath :=
  persistentPath config "used"

private def freePath (config : Config) : StoragePath :=
  persistentPath config "free"

private def epochPath (config : Config) : StoragePath :=
  persistentPath config "epoch"

private def draftPath (config : Config) : StoragePath :=
  runtimePath config "memory_draft"

private def objectPath (config : Config) : StoragePath :=
  runtimePath config "memory_object"

private def nextPath (config : Config) : StoragePath :=
  runtimePath config "memory_next"

private def addressPosition : Fin Heap.addressSchema.fields.length :=
  ⟨0, by simp [Heap.addressSchema]⟩

private def addressArgumentPath (config : Config) : StoragePath :=
  childKey (runtimePath config "memory_arg")
    (Heap.addressSchema.parameterKey addressPosition).text

private def macroSlot
    (config : Config) (suffix : List Nbt.PathSegment) : DataPath (.macro Heap.addressSchema) :=
  .index (slotsPath config) addressPosition suffix

private def scoreFromData (target : Score) (path : StoragePath) : Command .plain :=
  .store .result (.score target) (.data (.get path))

private def checkedFromData (config : Config) (target : Score) (path : StoragePath) : Command .plain :=
  .store .success (.score (pOk config)) (scoreFromData target path)

private def dataFromScore (path : StoragePath) (source : Score) : Command .plain :=
  .store .result (.storageI32 path) (.scoreboard (.get source))

private def macroCall
    (config : Config) (ref : FunctionRef (.macro Heap.addressSchema)) : Command .plain :=
  .functionWithStorage ref (⟨config.runtime, some (.key "memory_arg")⟩)

private def plainDef
    (ref : FunctionRef .plain) (commands : List (Command .plain)) :
    (kind : FunctionKind) × FunctionDef kind :=
  ⟨.plain, ⟨ref, .plain commands.toArray⟩⟩

private def macroLine
    (command : Command (.macro Heap.addressSchema))
    (used : 0 < command.parameterCount) : FunctionLine Heap.addressSchema :=
  .macro (MacroLine.ofCommand command used)

private def macroDef
    (ref : FunctionRef (.macro Heap.addressSchema))
    (lines : List (FunctionLine Heap.addressSchema)) :
    (kind : FunctionKind) × FunctionDef kind :=
  ⟨.macro Heap.addressSchema, ⟨ref, .macro lines.toArray⟩⟩

/-- Convert a positive one-based persistent address into Heap's zero-based macro index. -/
public def address (config : Config) (pointer : Int32 ⊕ Score) : List (Command .plain) :=
  match pointer with
  | .inl value => [.data (.setValue (addressArgumentPath config) (.int (value - 1)))]
  | .inr value => [
      .scoreboard (.set (pIndex config) (-1)),
      .scoreboard (.operation (pIndex config) .add value),
      .store .result (.storageI32 (addressArgumentPath config))
        (.scoreboard (.get (pIndex config)))]

public def source (config : Config) : MacroSource Heap.addressSchema :=
  ⟨config.runtime, some (.key "memory_arg")⟩

private def functionPath (suffix : String) : Except Diagnostic ResourcePath :=
  (ResourcePath.parse ("__oria/persistent/" ++ suffix)).mapError fun
    | .invalidResourceId text => .invalidResourceId text

public def ref (config : Config) (suffix : String) : Except Diagnostic (FunctionRef .plain) := do
  let path ← functionPath suffix
  pure (.ofId (.ofParts config.ns path))

private def macroRef
    (config : Config) (suffix : String) : Except Diagnostic (FunctionRef (.macro Heap.addressSchema)) := do
  let path ← functionPath suffix
  pure (.ofId (.ofParts config.ns path))

private structure Refs where
  allocate : FunctionRef .plain
  allocateFree : FunctionRef .plain
  allocateAppend : FunctionRef .plain
  replace : FunctionRef (.macro Heap.addressSchema)
  read : FunctionRef (.macro Heap.addressSchema)
  next : FunctionRef (.macro Heap.addressSchema)
  stamp : FunctionRef (.macro Heap.addressSchema)

private def makeRefs (config : Config) : Except Diagnostic Refs := do
  pure {
    allocate := ← ref config "allocate"
    allocateFree := ← ref config "allocate/free"
    allocateAppend := ← ref config "allocate/append"
    replace := ← macroRef config "replace"
    read := ← macroRef config "read"
    next := ← macroRef config "next"
    stamp := ← macroRef config "stamp" }

private def replaceBody (config : Config) : List (FunctionLine Heap.addressSchema) := [
  macroLine (.data (.setFrom (macroSlot config []) (draftPath config))) (by
    simp [macroSlot, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount])]

private def readBody (config : Config) : List (FunctionLine Heap.addressSchema) := [
  macroLine (.data (.setFrom (DataPath.static (objectPath config)) (macroSlot config []))) (by
    simp [macroSlot, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount])]

private def nextBody (config : Config) : List (FunctionLine Heap.addressSchema) := [
  macroLine (.data (.setFrom (macroSlot config [.key ⟨"next"⟩]) (DataPath.static (nextPath config)))) (by
    simp [macroSlot, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount])]

private def stampBody (config : Config) : List (FunctionLine Heap.addressSchema) := [
  macroLine (.when .positive (.matches (pEpoch config) (.exact 0))
    (.data (.setValue (macroSlot config [.key ⟨"mark"⟩]) (.int 0)))) (by
      simp [macroSlot, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]),
  macroLine (.when .positive (.matches (pEpoch config) (.exact 1))
    (.data (.setValue (macroSlot config [.key ⟨"mark"⟩]) (.int 1)))) (by
      simp [macroSlot, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount])]

private def allocateBody (config : Config) (refs : Refs) : List (Command .plain) := [
  .when .positive (.matches (panic config) (.exact 1)) .returnFail,
  .scoreboard (.set (oneScore config) 1),
  checkedFromData config (pEpoch config) (epochPath config),
  .when .negative (.matches (pOk config) (.exact 1)) (.scoreboard (.set (panic config) 1)),
  checkedFromData config (pFree config) (freePath config),
  .when .negative (.matches (pOk config) (.exact 1)) (.scoreboard (.set (panic config) 1)),
  .when .positive (.matches (pFree config) (.atLeast 1))
    (.returnRun (.function refs.allocateFree)),
  .returnRun (.function refs.allocateAppend)]

private def allocateFreeBody (config : Config) (refs : Refs) : List (Command .plain) :=
  [.when .positive (.matches (panic config) (.exact 1)) .returnFail,
    .scoreboard (.operation (pResult config) .assign (pFree config))] ++
    address config (.inr (pResult config)) ++ [
    macroCall config refs.read,
    checkedFromData config (pNext config) (childKey (objectPath config) "next"),
    .when .negative (.matches (pOk config) (.exact 1)) (.scoreboard (.set (panic config) 1)),
    macroCall config refs.replace,
    checkedFromData config (pUsed config) (usedPath config),
    .when .negative (.matches (pOk config) (.exact 1)) (.scoreboard (.set (panic config) 1)),
    dataFromScore (nextPath config) (pUsed config),
    macroCall config refs.next,
    macroCall config refs.stamp,
    dataFromScore (freePath config) (pNext config),
    dataFromScore (usedPath config) (pResult config),
    .when .positive (.matches (panic config) (.exact 1)) .returnFail,
    .returnValue 0]

private def allocateAppendBody (config : Config) (refs : Refs) : List (Command .plain) :=
  [
    .when .positive (.matches (panic config) (.exact 1)) .returnFail,
    checkedFromData config (pResult config) (slotsPath config),
    .when .negative (.matches (pOk config) (.exact 1)) (.scoreboard (.set (panic config) 1)),
    .when .positive (.matches (pResult config) (.exact 2147483647))
      (.scoreboard (.set (panic config) 1)),
    .when .positive (.matches (panic config) (.exact 1)) .returnFail,
    .scoreboard (.operation (pResult config) .add (oneScore config)),
  ] ++ address config (.inr (pResult config)) ++ [
    .data (.appendFrom (slotsPath config) (draftPath config)),
    checkedFromData config (pUsed config) (usedPath config),
    .when .negative (.matches (pOk config) (.exact 1)) (.scoreboard (.set (panic config) 1)),
    dataFromScore (nextPath config) (pUsed config),
    macroCall config refs.next,
    macroCall config refs.stamp,
    dataFromScore (usedPath config) (pResult config),
    .when .positive (.matches (panic config) (.exact 1)) .returnFail,
    .returnValue 0]

/-- Generate the allocator and its shared scalar-addressed object helpers. -/
public def generate (config : Config) :
    Except Diagnostic (List ((kind : FunctionKind) × FunctionDef kind)) := do
  let refs ← makeRefs config
  pure [
    plainDef refs.allocate (allocateBody config refs),
    plainDef refs.allocateFree (allocateFreeBody config refs),
    plainDef refs.allocateAppend (allocateAppendBody config refs),
    macroDef refs.replace (replaceBody config),
    macroDef refs.read (readBody config),
    macroDef refs.next (nextBody config),
    macroDef refs.stamp (stampBody config)]

end Oria.Lower.DP121.Persistent.Runtime
