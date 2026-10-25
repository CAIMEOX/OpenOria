module

public import Oria.Datapack.Resource
public import Oria.Command.Argument
public import Oria.IR.DP121.CommandPlan
public import Oria.IR.DP121.Storage

namespace Oria.Target.DP121

open Oria.Command

/-- A scoreboard holder token kept distinct from every other command token. -/
public structure ScoreHolder where
  private mk ::
  token : SyntaxToken
  deriving BEq, DecidableEq, Repr

namespace ScoreHolder

@[expose] public def ofToken (token : SyntaxToken) : ScoreHolder :=
  private_decl% ⟨token⟩

end ScoreHolder

/-- One exact scoreboard location. -/
public structure Score where
  holder : ScoreHolder
  objective : Objective
  deriving BEq, DecidableEq, Repr

public inductive Scoreboard where
  | objectiveAdd : Objective → Scoreboard
  | set : Score → Int32 → Scoreboard
  | add : Score → (amount : Int32) → (nonnegative : 0 ≤ amount) → Scoreboard
  | remove : Score → (amount : Int32) → (nonnegative : 0 ≤ amount) → Scoreboard
  | get : Score → Scoreboard
  | operation : Score → ScoreOp → Score → Scoreboard
  deriving BEq, DecidableEq, Repr

public inductive FunctionKind where
  | plain
  | macro (schema : MacroSchema)
  deriving DecidableEq

/-- A typed function identity distinguishing direct and with-storage calls. -/
public structure FunctionRef (kind : FunctionKind) where
  private mk ::
  id : Datapack.FunctionId

namespace FunctionRef

@[expose] public def ofId {kind : FunctionKind} (id : Datapack.FunctionId) : FunctionRef kind :=
  private_decl% ⟨id⟩

end FunctionRef

/-- The storage compound expected by one exact macro function schema. -/
public structure MacroSource (schema : MacroSchema) where
  storage : ResourceId
  path : Option Nbt.Path
  deriving Repr

/-- Storage paths may use a macro-bound list index or integer compound key. -/
public inductive DataPath : Mode → Type where
  | static {mode} : StoragePath → DataPath mode
  | index {schema : MacroSchema} :
      StoragePath → (i : Fin schema.fields.length) → List Nbt.PathSegment →
      (numeric : (schema.fields.get i).ty = .i32 := by first | rfl | simp_all) →
      DataPath (.macro schema)
  | key {schema : MacroSchema} :
      StoragePath → (i : Fin schema.fields.length) → List Nbt.PathSegment →
      (numeric : (schema.fields.get i).ty = .i32 := by first | rfl | simp_all) →
      DataPath (.macro schema)

public instance {mode : Mode} : Coe StoragePath (DataPath mode) := ⟨DataPath.static⟩

@[expose] public def DataPath.parameterCount {mode : Mode} : DataPath mode → Nat
  | .static _ => 0
  | .index _ _ _ _ | .key _ _ _ _ => 1

/-- Typed storage operations share the command's macro scope. -/
public inductive DataCommand (mode : Mode := .plain) where
  | setValue {tag : Nbt.Tag} : DataPath mode → Nbt.Value tag → DataCommand mode
  | setFrom : DataPath mode → DataPath mode → DataCommand mode
  | appendFrom : DataPath mode → DataPath mode → DataCommand mode
  | remove : DataPath mode → DataCommand mode
  | get : DataPath mode → DataCommand mode

@[expose] public def DataCommand.parameterCount {mode : Mode} : DataCommand mode → Nat
  | .setValue p _ | .remove p | .get p => p.parameterCount
  | .setFrom p q | .appendFrom p q => p.parameterCount + q.parameterCount

public inductive StoreKind where
  | success
  | result
  deriving BEq, DecidableEq, Repr

public inductive StoreTarget where
  | score : Score → StoreTarget
  | storageI32 : StoragePath → StoreTarget
  deriving Repr

public inductive Polarity where
  | positive
  | negative
  deriving BEq, DecidableEq, Repr

@[expose] public def BoundsOrdered
    (lower upper : Option Int32) : Prop :=
  match lower, upper with
  | some lower, some upper => lower ≤ upper
  | _, _ => True

public structure IntRange where
  private mk ::
  lower : Option Int32
  upper : Option Int32
  bounded : lower.isSome ∨ upper.isSome
  ordered : BoundsOrdered lower upper

namespace IntRange

@[expose] public def exact (value : Int32) : IntRange :=
  private_decl% ⟨some value, some value, by simp, by simp [BoundsOrdered]⟩

@[expose] public def atLeast (lower : Int32) : IntRange :=
  private_decl% ⟨some lower, none, by simp, True.intro⟩

@[expose] public def atMost (upper : Int32) : IntRange :=
  private_decl% ⟨none, some upper, by simp, True.intro⟩

@[expose] public def between
    (lower upper : Int32) (ordered : lower ≤ upper) : IntRange :=
  private_decl% ⟨some lower, some upper, by simp, ordered⟩

@[simp] public theorem between_ordered
    (lower upper : Int32) (ordered : lower ≤ upper) :
    BoundsOrdered (between lower upper ordered).lower
      (between lower upper ordered).upper :=
  (between lower upper ordered).ordered

@[simp] public theorem between_lower
    (lower upper : Int32) (ordered : lower ≤ upper) :
    (between lower upper ordered).lower = some lower :=
  private_decl% (by rfl)

@[simp] public theorem between_upper
    (lower upper : Int32) (ordered : lower ≤ upper) :
    (between lower upper ordered).upper = some upper :=
  private_decl% (by rfl)

end IntRange

public inductive ScoreRelation where
  | equal
  | less
  | lessOrEqual
  | greater
  | greaterOrEqual
  deriving BEq, DecidableEq, Repr

public inductive ScoreCondition where
  | matches : Score → IntRange → ScoreCondition
  | compare : Score → ScoreRelation → Score → ScoreCondition

/-- Typed DP121 commands; the mode controls whether bounded macro parameters may occur. -/
public inductive Command : Mode → Type where
  | scoreboard {mode} : Scoreboard → Command mode
  | data {mode} : DataCommand mode → Command mode
  | invoke {mode : Mode} {sig : Command.Signature} : Invocation mode sig → Command mode
  | native {mode : Mode} : FragmentInvocation mode → Command mode
  | execute {mode} : FragmentInvocation mode → FunctionRef .plain → Command mode
  | function {mode} : FunctionRef .plain → Command mode
  | schedule {mode} : FunctionRef .plain → Command mode
  | commandLimit {mode} : Command mode
  | functionWithStorage {schema : MacroSchema} {mode} :
      FunctionRef (.macro schema) → MacroSource schema → Command mode
  | when {mode} : Polarity → ScoreCondition → Command mode → Command mode
  | store {mode} : StoreKind → StoreTarget → Command mode → Command mode
  | returnValue {mode} : Int32 → Command mode
  | returnFail {mode} : Command mode
  | returnRun {mode} : Command mode → Command mode

namespace Command

@[expose] public def parameterCount {mode : Mode} : Command mode → Nat
  | .scoreboard _ | .function _ | .schedule _ | .commandLimit | .functionWithStorage _ _ |
      .returnValue _ | .returnFail => 0
  | .execute planned _ => planned.parameterCount
  | .invoke invocation => invocation.parameterCount
  | .native invocation => invocation.parameterCount
  | .data command => command.parameterCount
  | .when _ _ inner | .store _ _ inner | .returnRun inner => inner.parameterCount

end Command

/-- A macro-prefixed line carrying evidence that substitution occurs. -/
public structure MacroLine (schema : MacroSchema) where
  private mk ::
  command : Command (.macro schema)
  used : 0 < command.parameterCount

namespace MacroLine

@[expose] public def ofCommand {schema : MacroSchema}
    (command : Command (.macro schema))
    (used : 0 < command.parameterCount) : MacroLine schema :=
  private_decl% ⟨command, used⟩

end MacroLine

public inductive FunctionLine (schema : MacroSchema) where
  | static : Command .plain → FunctionLine schema
  | macro : MacroLine schema → FunctionLine schema

/-- A function body indexed by the call form required by its lines. -/
public inductive FunctionBody : FunctionKind → Type where
  | plain : Array (Command .plain) → FunctionBody .plain
  | macro {schema : MacroSchema} : Array (FunctionLine schema) → FunctionBody (.macro schema)

/-- Independently selected native command channels. -/
public structure Capture where
  success : Option Score := none
  result : Option Score := none

namespace Capture

@[expose] public def wrap {mode : Mode} (capture : Capture) (command : Command mode) : Command mode :=
  let command := match capture.result with
    | none => command
    | some score => .store .result (.score score) command
  match capture.success with
  | none => command
  | some score => .store .success (.score score) command

@[simp] public theorem parameterCount_wrap {mode : Mode} (capture : Capture) (command : Command mode) :
    (capture.wrap command).parameterCount = command.parameterCount := by
  rcases capture with ⟨success, result⟩
  cases success <;> cases result <;> rfl

end Capture

end Oria.Target.DP121
