module

public import Oria.IR.DP121.Syntax
public import Oria.IR.Common.I32

open Oria.Command (Objective ScoreOp)

namespace Oria.Target.DP121.Semantics

open Oria.Command

@[expose] public def CodecValue : {a : ObjTy} → HoleCodec a → Type
  | _, .i32 => Int32
  | _, .nativeNbt (t := t) => Nbt.ValueAt t

@[expose] public def CodecOption : {a : ObjTy} →
    (codec : HoleCodec a) → Option Nbt.Any → Option (CodecValue codec)
  | _, .i32, some ⟨.int, .int value⟩ => some value
  | _, .i32, _ => none
  | _, .nativeNbt (t := none), value => value
  | _, .nativeNbt (t := some t), some ⟨s, value⟩ =>
      if h : s = t then some (h ▸ value) else none
  | _, .nativeNbt (t := some _), none => none

@[expose] public def CodecValue.ofI32 : (codec : HoleCodec .i32) → Int32 → CodecValue codec
  | .i32, value => value

@[simp] public theorem CodecOption_some
    (codec : HoleCodec .i32) (value : Int32) :
    CodecOption codec (some ⟨.int, .int value⟩) = some (CodecValue.ofI32 codec value) := by
  cases codec
  rfl

public abbrev MacroValue (field : MacroField) :=
  CodecValue field.codec

public abbrev MacroEnv (schema : MacroSchema) :=
  Args MacroValue schema.fields

@[expose] public def ModeEnv : Mode → Type
  | .plain => Unit
  | .macro schema => MacroEnv schema

private def indexValue : (field : MacroField) → MacroValue field → field.ty = .i32 → Int
  | ⟨_, .i32⟩, value, _ => value.toInt
  | ⟨_, .nativeNbt⟩, _, h => nomatch h

/-- Substitute macro indices into ordinary storage paths before execution. -/
@[expose] public def dataPath {mode : Mode} (env : ModeEnv mode) : DataPath mode → StoragePath
  | .static path => path
  | .index (schema := schema) path i suffix numeric =>
      let index := private_decl% indexValue (schema.fields.get i) (env.get i) numeric
      ⟨path.storage, { path.path with tail := path.path.tail ++ .index index :: suffix }⟩
  | .key (schema := schema) path i suffix numeric =>
      let key := private_decl% indexValue (schema.fields.get i) (env.get i) numeric
      ⟨path.storage, { path.path with tail := path.path.tail ++ .key ⟨toString key⟩ :: suffix }⟩

@[expose] public def dataCommand {mode : Mode} (env : ModeEnv mode) : DataCommand mode → DataCommand
  | .setValue p v => .setValue (dataPath env p) v
  | .setFrom p q => .setFrom (dataPath env p) (dataPath env q)
  | .appendFrom p q => .appendFrom (dataPath env p) (dataPath env q)
  | .remove p => .remove (dataPath env p)
  | .get p => .get (dataPath env p)

/-- The observable channels of a native Minecraft command. -/
public structure Outcome where
  success : Bool
  result : Int32

namespace Outcome

@[expose] public def decode (outcome : Outcome) : Option Int32 :=
  if outcome.success then some outcome.result else none

@[expose] public def succeeded (result : Int32) : Outcome :=
  { success := true, result }

@[expose] public def failed : Outcome :=
  { success := false, result := 0 }

end Outcome

public inductive Flow where
  | next : Outcome → Flow
  | returned : Outcome → Flow

namespace Flow

@[expose] public def outcome : Flow → Outcome
  | .next outcome | .returned outcome => outcome

end Flow

public structure PrimitiveResult (S Trace : Type) where
  state : S
  outcome : Outcome
  trace : Array Trace

public structure ExternalResult (Scores Storage Trace : Type) where
  scores : Scores
  storage : Storage
  outcome : Outcome
  trace : Array Trace

public structure OperationResult where
  target : Option Int32
  source : Option Int32
  outcome : Outcome

@[expose] public def materializeScore : Option Int32 → Int32
  | none => 0
  | some value => value

/-- Canonical Java scoreboard operation semantics, including floor division and failure. -/
@[expose] public def scoreOperation
    (operator : ScoreOp) (left right : Option Int32) : OperationResult :=
  let left := materializeScore left
  let right := materializeScore right
  match operator with
  | .divide =>
      match Oria.I32.divide left right with
      | none => ⟨some left, some right, .failed⟩
      | some value => ⟨some value, some right, .succeeded value⟩
  | .modulo =>
      match Oria.I32.divide left right with
      | none => ⟨some left, some right, .failed⟩
      | some quotient =>
          let value := left - quotient * right
          ⟨some value, some right, .succeeded value⟩
  | .assign => ⟨some right, some right, .succeeded right⟩
  | .add => ⟨some (left + right), some right, .succeeded (left + right)⟩
  | .subtract => ⟨some (left - right), some right, .succeeded (left - right)⟩
  | .multiply => ⟨some (left * right), some right, .succeeded (left * right)⟩
  | .minimum => ⟨some (min left right), some right, .succeeded (min left right)⟩
  | .maximum => ⟨some (max left right), some right, .succeeded (max left right)⟩
  | .swap => ⟨some right, some left, .succeeded right⟩

@[simp] public theorem scoreOperation_divide_zero (value : Int32) :
    scoreOperation .divide (some value) (some 0) =
      ⟨some value, some 0, .failed⟩ := by
  simp [scoreOperation, materializeScore, Oria.I32.divide]

/-- Initialized scoreboard division has exactly the language's normal/failure result. -/
public theorem scoreOperation_divide_decode (left right : Int32) :
    (scoreOperation .divide (some left) (some right)).outcome.decode = Oria.I32.divide left right := by
  simp only [scoreOperation, materializeScore]
  cases Oria.I32.divide left right <;> rfl

@[simp] public theorem scoreOperation_modulo_zero (value : Int32) :
    scoreOperation .modulo (some value) (some 0) =
      ⟨some value, some 0, .failed⟩ := by
  simp [scoreOperation, materializeScore]

@[simp] public theorem scoreOperation_missing_add :
    scoreOperation .add none none =
      ⟨some 0, some 0, .succeeded 0⟩ := by
  simp [scoreOperation, materializeScore]

@[simp] public theorem scoreOperation_missing_divide :
    scoreOperation .divide none none =
      ⟨some 0, some 0, .failed⟩ := by
  simp [scoreOperation, materializeScore]

/-- External Minecraft operations consumed by the typed command semantics. -/
public structure Model where
  Scores : Type
  Storage : Type
  Trace : Type
  objectiveExists : Objective → Scores → Bool
  score? : Score → Scores → Option Int32
  storageI32? : StoragePath → Storage → Option Int32
  storageNbt? : StoragePath → Storage → Option Nbt.Any
  scoreboard : Scoreboard → Scores → PrimitiveResult Scores Trace
  /-- External NBT primitive oracle; target simulation supplies its compatibility theorem. -/
  data : DataCommand → Storage → PrimitiveResult Storage Trace
  invoke : {mode : Mode} → {sig : Command.Signature} →
    Invocation mode sig → ModeEnv mode → Scores → Storage →
      ExternalResult Scores Storage Trace
  native : {mode : Mode} → FragmentInvocation mode → ModeEnv mode → Scores → Storage →
      ExternalResult Scores Storage Trace
  schedule : FunctionRef .plain → Scores → Storage → ExternalResult Scores Storage Trace
  commandLimit : Scores → PrimitiveResult Scores Trace
  execute : {mode : Mode} → FragmentInvocation mode → ModeEnv mode →
    (Scores → Storage → Option (ExternalResult Scores Storage Trace)) →
    Scores → Storage → Option (ExternalResult Scores Storage Trace)
  condition : ScoreCondition → Scores → Bool
  storeScore : Score → Int32 → Scores → Scores
  storeStorage : StoragePath → Int32 → Storage → Storage
  decodeMacro : {schema : MacroSchema} →
    MacroSource schema → Storage → Option (MacroEnv schema)
  macroField? : {schema : MacroSchema} →
    (source : MacroSource schema) →
    (position : Fin schema.fields.length) →
    Storage → Option (MacroValue (schema.fields.get position))
  emptyFunction : Outcome

@[expose] public def macroParameterPath {schema : MacroSchema}
    (source : MacroSource schema)
    (position : Fin schema.fields.length) : StoragePath :=
  let key := schema.parameterKey position
  let path := match source.path with
    | none => Nbt.Path.key key.text
    | some path => path.child (.key key)
  ⟨source.storage, path⟩

@[expose] public def IntRange.contains (range : IntRange) (value : Int32) : Bool :=
  let lower := match range.lower with
    | none => true
    | some lower => decide (lower ≤ value)
  let upper := match range.upper with
    | none => true
    | some upper => decide (value ≤ upper)
  lower && upper

@[expose] public def ScoreRelation.holds
    (relation : ScoreRelation) (left right : Int32) : Bool :=
  match relation with
  | .equal => left == right
  | .less => decide (left < right)
  | .lessOrEqual => decide (left ≤ right)
  | .greater => decide (left > right)
  | .greaterOrEqual => decide (left ≥ right)

@[expose] public def operationReady
    (model : Model) (target source : Score) (scores : model.Scores) : Bool :=
  model.objectiveExists target.objective scores &&
    model.objectiveExists source.objective scores

/-- Observable equations required of a DP121 command model. -/
public structure LawfulModel (model : Model) : Prop where
  scoreImpliesObjective : ∀ score scores value,
    model.score? score scores = some value →
      model.objectiveExists score.objective scores = true
  objectiveAddOutcome : ∀ objective scores,
    (model.scoreboard (.objectiveAdd objective) scores).outcome =
      if model.objectiveExists objective scores then .failed else .succeeded 1
  objectiveAddObjectives : ∀ objective scores observed,
    model.objectiveExists observed
        (model.scoreboard (.objectiveAdd objective) scores).state =
      if observed = objective then true else model.objectiveExists observed scores
  objectiveAddScores : ∀ objective scores observed,
    model.score? observed (model.scoreboard (.objectiveAdd objective) scores).state =
      model.score? observed scores
  setOutcome : ∀ target value scores,
    (model.scoreboard (.set target value) scores).outcome =
      if model.objectiveExists target.objective scores then .succeeded value else .failed
  setScores : ∀ target value scores observed,
    model.score? observed (model.scoreboard (.set target value) scores).state =
      if model.objectiveExists target.objective scores then
        if observed = target then some value else model.score? observed scores
      else model.score? observed scores
  setObjectives : ∀ target value scores (observed : Score),
    model.objectiveExists observed.objective
        (model.scoreboard (.set target value) scores).state =
      model.objectiveExists observed.objective scores
  addOutcome : ∀ target amount h scores,
    (model.scoreboard (.add target amount h) scores).outcome =
      if model.objectiveExists target.objective scores then
        .succeeded ((model.score? target scores).getD 0 + amount) else .failed
  addScores : ∀ target amount h scores observed,
    model.score? observed (model.scoreboard (.add target amount h) scores).state =
      if model.objectiveExists target.objective scores then
        if observed = target then some ((model.score? target scores).getD 0 + amount)
        else model.score? observed scores
      else model.score? observed scores
  addObjectives : ∀ target amount h scores observed,
    model.objectiveExists observed (model.scoreboard (.add target amount h) scores).state =
      model.objectiveExists observed scores
  removeOutcome : ∀ target amount h scores,
    (model.scoreboard (.remove target amount h) scores).outcome =
      if model.objectiveExists target.objective scores then
        .succeeded ((model.score? target scores).getD 0 - amount) else .failed
  removeScores : ∀ target amount h scores observed,
    model.score? observed (model.scoreboard (.remove target amount h) scores).state =
      if model.objectiveExists target.objective scores then
        if observed = target then some ((model.score? target scores).getD 0 - amount)
        else model.score? observed scores
      else model.score? observed scores
  removeObjectives : ∀ target amount h scores observed,
    model.objectiveExists observed (model.scoreboard (.remove target amount h) scores).state =
      model.objectiveExists observed scores
  getOutcome : ∀ target scores,
    (model.scoreboard (.get target) scores).outcome =
      match model.score? target scores with
      | none => .failed
      | some value => .succeeded value
  getScores : ∀ target scores observed,
    model.score? observed (model.scoreboard (.get target) scores).state =
      model.score? observed scores
  getObjectives : ∀ target scores observed,
    model.objectiveExists observed
        (model.scoreboard (.get target) scores).state =
      model.objectiveExists observed scores
  operationOutcome : ∀ target operator source scores,
    (model.scoreboard (.operation target operator source) scores).outcome =
      if operationReady model target source scores then
        (scoreOperation operator (model.score? target scores)
          (model.score? source scores)).outcome
      else .failed
  operationScores : ∀ target operator source scores observed,
    model.score? observed (model.scoreboard (.operation target operator source) scores).state =
      if operationReady model target source scores then
        let expected := scoreOperation operator (model.score? target scores)
          (model.score? source scores)
        if observed = target then expected.target
        else if observed = source then expected.source
        else model.score? observed scores
      else model.score? observed scores
  operationObjectives : ∀ target operator source scores observed,
    model.objectiveExists observed
        (model.scoreboard (.operation target operator source) scores).state =
      model.objectiveExists observed scores
  matchesCondition : ∀ score range scores,
    model.condition (.matches score range) scores =
      match model.score? score scores with
      | none => false
      | some value => IntRange.contains range value
  compareCondition : ∀ left relation right scores,
    model.condition (.compare left relation right) scores =
      match model.score? left scores, model.score? right scores with
      | some left, some right => ScoreRelation.holds relation left right
      | _, _ => false
  storeScore : ∀ target value scores observed,
    model.score? observed (model.storeScore target value scores) =
      if observed = target then some value else model.score? observed scores
  storeStorage : ∀ target value storage observed,
    model.storageI32? observed (model.storeStorage target value storage) =
      if observed = target then some value else model.storageI32? observed storage
  macroFieldStorage : ∀ {schema} (source : MacroSource schema) storage position,
    model.macroField? source position storage =
      CodecOption (schema.fields.get position).codec
        (model.storageNbt? (macroParameterPath source position) storage)
  decodeSome : ∀ {schema} (source : MacroSource schema) storage env,
    model.decodeMacro source storage = some env →
      ∀ position, model.macroField? source position storage = some (env.get position)
  decodeComplete : ∀ {schema} (source : MacroSource schema) storage env,
    (∀ position, model.macroField? source position storage = some (env.get position)) →
      model.decodeMacro source storage = some env

public theorem LawfulModel.decode_missing {model : Model} {schema : MacroSchema}
    (lawful : LawfulModel model)
    (source : MacroSource schema)
    (storage : model.Storage)
    (position : Fin schema.fields.length)
    (missing : model.macroField? source position storage = none) :
    model.decodeMacro source storage = none := by
  match decoded : model.decodeMacro source storage with
  | none => rfl
  | some env =>
      have present := lawful.decodeSome source storage env decoded position
      rw [missing] at present
      contradiction

/-- A total typed function catalogue used by direct and with-storage calls. -/
public structure Code where
  body : {kind : FunctionKind} → FunctionRef kind → FunctionBody kind

@[expose] public def FunctionKind.mode : FunctionKind → Mode
  | .plain => .plain
  | .macro schema => .macro schema

public abbrev FunctionEnv (kind : FunctionKind) :=
  ModeEnv (FunctionKind.mode kind)

public structure State (model : Model) where
  scores : model.Scores
  storage : model.Storage
  trace : Array model.Trace

public structure Result (model : Model) where
  state : State model
  flow : Flow

namespace State

@[expose] public def applyScore {model : Model}
    (state : State model)
    (result : PrimitiveResult model.Scores model.Trace) : State model :=
  { state with scores := result.state, trace := state.trace ++ result.trace }

@[expose] public def applyData {model : Model}
    (state : State model)
    (result : PrimitiveResult model.Storage model.Trace) : State model :=
  { state with storage := result.state, trace := state.trace ++ result.trace }

@[expose] public def applyExternal {model : Model}
    (state : State model)
    (result : ExternalResult model.Scores model.Storage model.Trace) : State model :=
  { scores := result.scores
    storage := result.storage
    trace := state.trace ++ result.trace }

end State

@[expose] public def StoreKind.value (kind : StoreKind) (outcome : Outcome) : Int32 :=
  match kind with
  | .success => if outcome.success then 1 else 0
  | .result => outcome.result

@[expose] public def Polarity.accepts (polarity : Polarity) (condition : Bool) : Bool :=
  match polarity with
  | .positive => condition
  | .negative => !condition

@[expose] public def State.store
    (model : Model)
    (kind : StoreKind)
    (target : StoreTarget)
    (outcome : Outcome)
    (state : State model) : State model :=
  let value := Oria.Target.DP121.Semantics.StoreKind.value kind outcome
  match target with
  | .score score => { state with scores := model.storeScore score value state.scores }
  | .storageI32 path =>
      { state with storage := model.storeStorage path value state.storage }

mutual
  /-- Evaluate one typed DP121 command within its already-decoded macro environment. -/
  @[expose] public def evalCommand {mode : Mode}
      (model : Model)
      (code : Code)
      (fuel : Nat)
      (env : ModeEnv mode)
      (state : State model)
      (command : Command mode) : Option (Result model) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match command with
        | .scoreboard command =>
            let result := model.scoreboard command state.scores
            some ⟨state.applyScore result, .next result.outcome⟩
        | .commandLimit =>
            let result := model.commandLimit state.scores
            some ⟨state.applyScore result, .next result.outcome⟩
        | .schedule ref =>
            let result := model.schedule ref state.scores state.storage
            some ⟨state.applyExternal result, .next result.outcome⟩
        | .data command =>
            let result := model.data (dataCommand env command) state.storage
            some ⟨state.applyData result, .next result.outcome⟩
        | .invoke invocation =>
            let result := model.invoke invocation env state.scores state.storage
            some ⟨state.applyExternal result, .next result.outcome⟩
        | .native invocation =>
            let result := model.native invocation env state.scores state.storage
            some ⟨state.applyExternal result, .next result.outcome⟩
        | .execute chain callee => do
            let result ← model.execute chain env (fun scores storage => do
              let result ← evalBody model code fuel (kind := .plain) ()
                ⟨scores, storage, #[]⟩ (code.body callee)
              pure ⟨result.state.scores, result.state.storage,
                result.flow.outcome, result.state.trace⟩) state.scores state.storage
            pure ⟨state.applyExternal result, .next result.outcome⟩
        | .function callee =>
            match evalBody model code fuel (kind := .plain) () state (code.body callee) with
            | none => none
            | some result => some ⟨result.state, .next result.flow.outcome⟩
        | .functionWithStorage callee source =>
            match model.decodeMacro source state.storage with
            | none => some ⟨state, .next .failed⟩
            | some macroEnv =>
                match evalBody model code fuel (kind := .macro _) macroEnv state
                    (code.body callee) with
                | none => none
                | some result => some ⟨result.state, .next result.flow.outcome⟩
        | .when polarity condition inner =>
            if Oria.Target.DP121.Semantics.Polarity.accepts polarity
                (model.condition condition state.scores) then
              evalCommand model code fuel env state inner
            else
              some ⟨state, .next .failed⟩
        | .store kind target inner =>
            match evalCommand model code fuel env state inner with
            | none => none
            | some result =>
                some ⟨State.store model kind target result.flow.outcome result.state,
                  result.flow⟩
        | .returnValue value => some ⟨state, .returned (.succeeded value)⟩
        | .returnFail => some ⟨state, .returned .failed⟩
        | .returnRun inner =>
            match evalCommand model code fuel env state inner with
            | none => none
            | some result => some ⟨result.state, .returned result.flow.outcome⟩

  /-- Evaluate a complete function body in source order. -/
  @[expose] public def evalBody {kind : FunctionKind}
      (model : Model)
      (code : Code)
      (fuel : Nat)
      (env : FunctionEnv kind)
      (state : State model)
      (body : FunctionBody kind) : Option (Result model) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match body, env with
        | .plain commands, () =>
            evalPlainLines model code fuel commands.toList state model.emptyFunction
        | .macro lines, macroEnv =>
            evalMacroLines model code fuel lines.toList macroEnv state model.emptyFunction

  @[expose] public def evalPlainLines
      (model : Model)
      (code : Code)
      (fuel : Nat)
      (commands : List (Command .plain))
      (state : State model)
      (last : Outcome) : Option (Result model) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match commands with
        | [] => some ⟨state, .next last⟩
        | command :: rest =>
            match evalCommand model code fuel (mode := .plain) () state command with
            | none => none
            | some result =>
                match result.flow with
                | .returned outcome => some ⟨result.state, .next outcome⟩
                | .next outcome =>
                    evalPlainLines model code fuel rest result.state outcome

  @[expose] public def evalMacroLines {schema : MacroSchema}
      (model : Model)
      (code : Code)
      (fuel : Nat)
      (lines : List (FunctionLine schema))
      (env : MacroEnv schema)
      (state : State model)
      (last : Outcome) : Option (Result model) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match lines with
        | [] => some ⟨state, .next last⟩
        | line :: rest =>
            let evaluated := match line with
              | .static command =>
                  evalCommand model code fuel (mode := .plain) () state command
              | .macro line =>
                  evalCommand model code fuel (mode := .macro schema) env state line.command
            match evaluated with
            | none => none
            | some result =>
                match result.flow with
                | .returned outcome => some ⟨result.state, .next outcome⟩
                | .next outcome =>
                    evalMacroLines model code fuel rest env result.state outcome
end

end Oria.Target.DP121.Semantics
