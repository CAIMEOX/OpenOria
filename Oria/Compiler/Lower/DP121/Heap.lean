module

public import Oria.IR.DP121.Program
public import Oria.IR.Representation.Syntax
public import Oria.Compiler.Lower.DP121.Stack
import Oria.Nbt.Syntax

namespace Oria.Lower.DP121.Heap

open Oria.Target.DP121

public structure Config where
  storage : ResourceId
  objective : Oria.Command.Objective

private def score (config : Config) (name : Oria.Command.SyntaxToken) : Score :=
  ⟨.ofToken name, config.objective⟩

private def counter (config : Config) : Score := score config "#heap_count"
private def index (config : Config) : Score := score config "#heap_index"

private def path (config : Config) (key : String) : StoragePath :=
  ⟨config.storage, .key key⟩

public def begin (config : Config) : List (Command .plain) := [
  .data (.setValue (path config "arena") (nbt% [])),
  .scoreboard (.set (counter config) 0)]

public def finish (config : Config) : List (Command .plain) :=
  (["arena", "draft", "heap_arg", "nbt_input"].map fun key =>
    .data (.remove (path config key))) ++
    [.data (.setValue (path config "macro") (nbt% {}))]

/-- Every ABI entry owns one arena; ordinary calls execute within that arena. -/
public def invoke (config : Config) (target : FunctionRef .plain) : List (Command .plain) :=
  begin config ++ [.function target] ++ finish config

public def writeWord (path : StoragePath) : Int32 ⊕ Score → Command .plain
  | .inl value => .data (.setValue path (.int value))
  | .inr score => .store .result (.storageI32 path) (.scoreboard (.get score))

/-- Append the fully initialized draft and publish its negative arena pointer. -/
public def publish (config : Config) (target : Place) : List (Command .plain) :=
  let out := match target with | .score score => score | .storage _ => index config
  [ .data (.appendFrom (path config "arena") (path config "draft")),
    .scoreboard (.add (counter config) 1 (by decide)),
    .scoreboard (.set out 0),
    .scoreboard (.operation out .subtract (counter config))] ++
    (if target == .score out then [] else [Stack.move ⟨target, .loc (.score out)⟩])

/-- Initialize the complete immutable object before appending it and publishing its pointer. -/
public def allocate {n : Nat} (config : Config) (layout : Representation.HeapLayout n)
    (values : Vector (Transfer.Source Place) n) (target : Place) : List (Command .plain) :=
  let draft := path config "draft"
  let initial := nbt% {tag: $(layout.tag), payload: $(Array.replicate n (0 : Int32))}
  let fields := (List.finRange n).map fun i =>
    Stack.move ⟨.storage ⟨draft.storage, (draft.path.child (.key ⟨"payload"⟩)).child (.index i.val)⟩,
      values.get i⟩
  [.data (.setValue draft initial)] ++ fields ++ publish config target

@[expose, simp] public def addressSchema : MacroSchema := .ofFields [⟨.i32, .i32⟩]

/-- A zero-based list index is derived from the negative, one-based arena reference. -/
public def address (config : Config) (pointer : Int32 ⊕ Score) : List (Command .plain) :=
  let target : StoragePath :=
    ⟨config.storage, (Nbt.Path.key "heap_arg").child
      (.key (addressSchema.parameterKey ⟨0, by simp [addressSchema]⟩))⟩
  match pointer with
  | .inl pointer => [.data (.setValue target (.int (-1 - pointer)))]
  | .inr pointer => [
      .scoreboard (.set (index config) (-1)),
      .scoreboard (.operation (index config) .subtract pointer),
      .store .result (.storageI32 target) (.scoreboard (.get (index config)))]

/-- One helper projects only demanded fields; its sole macro argument is the object index. -/
public def reader (config : Config) (ref : FunctionRef (.macro addressSchema))
    (fields : List (List Nbt.PathSegment × Place)) : FunctionDef (.macro addressSchema) :=
  let lines := fields.map fun (suffix, target) =>
    let source : DataPath (.macro addressSchema) :=
      .index (path config "arena") ⟨0, by simp [addressSchema]⟩ suffix
    let command : Command (.macro addressSchema) := match target with
      | .score target => .store .result (.score target) (.data (.get source))
      | .storage target => .data (.setFrom target source)
    FunctionLine.macro (.ofCommand command (by
      cases target <;>
        simp [command, source, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]))
  ⟨ref, .macro lines.toArray⟩

public def source (config : Config) : MacroSource addressSchema :=
  ⟨config.storage, some (.key "heap_arg")⟩

end Oria.Lower.DP121.Heap
