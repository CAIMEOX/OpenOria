module

public import Oria.IR.DP121.Semantics
public meta import Oria.IR.DP121.Semantics
import Init.Data.Array.Lemmas

open Oria.Command (Objective ScoreOp)

namespace Oria.Proofs.DP121Semantics

open Oria Oria.Target.DP121 Oria.Target.DP121.Semantics

theorem status_wrap_runs_once {mode : Mode} {model : Model} {code : Code} {fuel : Nat}
    {env : ModeEnv mode}
    {state : State model} {command : Command mode} {target : Score}
    {result : Result model}
    (evaluated : evalCommand model code fuel env state command = some result) :
    evalCommand model code (fuel + 1) env state
        ((({ success := some target } : Capture)).wrap command) =
      some ⟨State.store model .success (.score target)
        result.flow.outcome result.state, result.flow⟩ := by
  cases fuel with
  | zero => simp [evalCommand] at evaluated
  | succ fuel =>
      change (match evalCommand model code (fuel + 1) env state command with
        | none => none
        | some result => some ({
            state := State.store model .success (.score target)
              result.flow.outcome result.state
            flow := result.flow } : Result model)) = _
      rw [evaluated]

theorem payload_wrap_runs_once {mode : Mode} {model : Model} {code : Code} {fuel : Nat}
    {env : ModeEnv mode}
    {state : State model} {command : Command mode} {success resultTarget : Score}
    {result : Result model}
    (evaluated : evalCommand model code fuel env state command = some result) :
    evalCommand model code (fuel + 2) env state
        ((({ success := some success, result := some resultTarget } : Capture)).wrap command) =
      some ⟨State.store model .success (.score success) result.flow.outcome <|
        State.store model .result (.score resultTarget) result.flow.outcome result.state,
        result.flow⟩ := by
  cases fuel with
  | zero => simp [evalCommand] at evaluated
  | succ fuel =>
      change (match
        (match evalCommand model code (fuel + 1) env state command with
        | none => none
        | some result => some ({
            state := State.store model .result (.score resultTarget)
              result.flow.outcome result.state
            flow := result.flow } : Result model)) with
        | none => none
        | some result => some ({
            state := State.store model .success (.score success)
              result.flow.outcome result.state
            flow := result.flow } : Result model)) = _
      rw [evaluated]

theorem return_run_forwards {mode : Mode} {model : Model} {code : Code} {fuel : Nat}
    {env : ModeEnv mode}
    {state : State model} {command : Command mode} {result : Result model}
    (evaluated : evalCommand model code fuel env state command = some result) :
    evalCommand model code (fuel + 1) env state (.returnRun command) =
      some ⟨result.state, .returned result.flow.outcome⟩ := by
  cases fuel with
  | zero => simp [evalCommand] at evaluated
  | succ fuel =>
      change (match evalCommand model code (fuel + 1) env state command with
        | none => none
        | some result => some ({
            state := result.state
            flow := .returned result.flow.outcome } : Result model)) = _
      rw [evaluated]

theorem successful_zero_is_retained : (Outcome.succeeded 0).decode = some 0 :=
  rfl

example : Oria.I32.divide (-7) 3 = some (-3 : Int32) := by
  native_decide

example : (scoreOperation .modulo (some (-7)) (some 3)).outcome = .succeeded 2 := by
  rfl

example (value : Int32) :
    scoreOperation .divide (some value) (some 0) =
      ⟨some value, some 0, .failed⟩ :=
  scoreOperation_divide_zero value

private abbrev Scores := Score → Int32
private abbrev Storage := StoragePath → Int32

private def updateScore
    (scores : Scores) (target : Score) (value : Int32) : Scores :=
  fun score => if score = target then value else scores score

private def updateStorage
    (storage : Storage) (target : StoragePath) (value : Int32) : Storage :=
  fun path => if path = target then value else storage path

private def scoreResult (command : Scoreboard) (scores : Scores) :
    PrimitiveResult Scores Nat :=
  match command with
  | .objectiveAdd _ => ⟨scores, .failed, #[0]⟩
  | .set target value =>
      ⟨updateScore scores target value, .succeeded value, #[0]⟩
  | .add target amount _ =>
      let value := scores target + amount
      ⟨updateScore scores target value, .succeeded value, #[0]⟩
  | .remove target amount _ =>
      let value := scores target - amount
      ⟨updateScore scores target value, .succeeded value, #[0]⟩
  | .get target => ⟨scores, .succeeded (scores target), #[0]⟩
  | .operation target operator source =>
      let expected := scoreOperation operator (some (scores target)) (some (scores source))
      let scores := match expected.target, expected.source with
        | some targetValue, some sourceValue =>
            if target = source then updateScore scores target targetValue
            else updateScore (updateScore scores target targetValue) source sourceValue
        | _, _ => scores
      ⟨scores, expected.outcome, #[0]⟩

private def scoreCondition
    (condition : ScoreCondition) (scores : Scores) : Bool :=
  match condition with
  | .matches score range =>
      Oria.Target.DP121.Semantics.IntRange.contains range (scores score)
  | .compare left relation right =>
      Oria.Target.DP121.Semantics.ScoreRelation.holds relation
        (scores left) (scores right)

private def macroValue {schema : MacroSchema}
    (source : MacroSource schema)
    (storage : Storage)
    (position : Fin schema.fields.length) :
    Option (MacroValue (schema.fields.get position)) :=
  CodecOption (schema.fields.get position).codec
    (some ⟨.int, .int (storage (macroParameterPath source position))⟩)

private def macroEnv {schema : MacroSchema}
    (source : MacroSource schema) (storage : Storage) : Option (MacroEnv schema) :=
  if h : ∀ i, (macroValue source storage i).isSome then
    some (Args.tabulate schema.fields (fun i => (macroValue source storage i).get (h i)))
  else none

private def countingModel : Model where
  Scores := Scores
  Storage := Storage
  Trace := Nat
  objectiveExists := fun _ _ => true
  score? := fun score scores => some (scores score)
  storageI32? := fun path storage => some (storage path)
  storageNbt? := fun path storage => some ⟨.int, .int (storage path)⟩
  scoreboard := scoreResult
  data := fun _ storage => ⟨storage, .succeeded 0, #[0]⟩
  invoke := fun _ _ scores storage => ⟨scores, storage, .succeeded 0, #[0]⟩
  native := fun _ _ scores storage => ⟨scores, storage, .succeeded 0, #[0]⟩
  schedule := fun _ scores storage => ⟨scores, storage, .succeeded 0, #[0]⟩
  commandLimit := fun scores => ⟨scores, .succeeded 65536, #[0]⟩
  execute := fun _ _ body scores storage => body scores storage
  condition := scoreCondition
  storeScore := fun target value scores => updateScore scores target value
  storeStorage := fun target value storage => updateStorage storage target value
  decodeMacro := macroEnv
  macroField? := fun source position storage => macroValue source storage position
  emptyFunction := .succeeded 0

private def emptyCode : Code where
  body := fun {kind} _ => match kind with
    | .plain => .plain #[]
    | .macro _ => .macro #[]

private theorem scoreOperation_some
    (operator : ScoreOp) (left right : Int32) :
    ∃ target source outcome,
      scoreOperation operator (some left) (some right) =
        ⟨some target, some source, outcome⟩ := by
  cases operator <;> simp [scoreOperation] <;>
    split <;> simp_all

private theorem countingModel_lawful : LawfulModel countingModel where
  scoreImpliesObjective := by
    intro score scores value present
    rfl
  objectiveAddOutcome := by
    intro objective scores
    rfl
  objectiveAddObjectives := by
    intro objective scores observed
    simp [countingModel]
  objectiveAddScores := by
    intro objective scores observed
    rfl
  setOutcome := by
    intro target value scores
    rfl
  setScores := by
    intro target value scores observed
    by_cases same : observed = target
    · subst observed
      simp [countingModel, scoreResult, updateScore]
    · simp [countingModel, scoreResult, updateScore, same]
  setObjectives := by
    intro target value scores observed
    rfl
  addOutcome := by intros; rfl
  addScores := by
    intro target amount h scores observed
    by_cases same : observed = target <;> simp [countingModel, scoreResult, updateScore, same]
  addObjectives := by intros; rfl
  removeOutcome := by intros; rfl
  removeScores := by
    intro target amount h scores observed
    by_cases same : observed = target <;> simp [countingModel, scoreResult, updateScore, same]
  removeObjectives := by intros; rfl
  getOutcome := by
    intro target scores
    rfl
  getScores := by
    intro target scores observed
    rfl
  getObjectives := by
    intro target scores observed
    rfl
  operationOutcome := by
    intro target operator source scores
    simp [operationReady, countingModel, scoreResult]
  operationScores := by
    intro target operator source scores observed
    obtain ⟨targetValue, sourceValue, outcome, exact⟩ :=
      scoreOperation_some operator (scores target) (scores source)
    simp only [countingModel, operationReady, Bool.true_and, scoreResult, exact]
    by_cases same : target = source
    · subst source
      by_cases atTarget : observed = target
      · subst observed
        simp [updateScore]
      · simp [atTarget, updateScore]
    · by_cases atTarget : observed = target
      · subst observed
        simp [same, updateScore]
      · by_cases atSource : observed = source
        · subst observed
          simp [same, atTarget, updateScore]
        · simp [same, atTarget, atSource, updateScore]
  operationObjectives := by
    intro target operator source scores observed
    rfl
  matchesCondition := by
    intro score range scores
    rfl
  compareCondition := by
    intro left relation right scores
    rfl
  storeScore := by
    intro target value scores observed
    by_cases same : observed = target
    · subst observed
      simp [countingModel, updateScore]
    · simp [countingModel, updateScore, same]
  storeStorage := by
    intro target value storage observed
    by_cases same : observed = target
    · subst observed
      simp [countingModel, updateStorage]
    · simp [countingModel, updateStorage, same]
  macroFieldStorage := by
    intro schema source storage position
    simp [countingModel, macroValue]
  decodeSome := by
    intro schema source storage env decoded
    change macroEnv source storage = some env at decoded
    unfold macroEnv at decoded
    split at decoded
    · have equal := Option.some.inj decoded
      subst env
      intro position
      simp [countingModel]
    · cases decoded
  decodeComplete := by
    intro schema source storage env complete
    have present : ∀ i, (macroValue source storage i).isSome := by
      intro i
      have equal := complete i
      change macroValue source storage i = some (env.get i) at equal
      simp [equal]
    change macroEnv source storage = some env
    simp only [macroEnv, dif_pos present]
    apply congrArg some
    apply Args.ext
    intro position
    have equal := complete position
    change macroValue source storage position = some (env.get position) at equal
    simp [equal]

private theorem lawful_set_observation
    (scores : Scores) (target : Score) (value : Int32) :
    countingModel.score? target
        (countingModel.scoreboard (.set target value) scores).state = some value := by
  rw [countingModel_lawful.setScores]
  simp [countingModel]

private theorem lawful_get_observation
    (scores : Scores) (target : Score) :
    (countingModel.scoreboard (.get target) scores).outcome =
      .succeeded (scores target) := by
  rw [countingModel_lawful.getOutcome]
  rfl

private theorem lawful_store_observation
    (scores : Scores) (target : Score) (value : Int32) :
    countingModel.score? target (countingModel.storeScore target value scores) =
      some value := by
  rw [countingModel_lawful.storeScore]
  simp

private theorem lawful_condition_observation
    (scores : Scores) (target : Score) (range : IntRange) :
    countingModel.condition (.matches target range) scores =
      IntRange.contains range (scores target) := by
  rw [countingModel_lawful.matchesCondition]
  rfl

private theorem lawful_decode_observation {schema : MacroSchema}
    (source : MacroSource schema)
    (storage : Storage)
    (position : Fin schema.fields.length) :
    countingModel.macroField? source position storage =
      CodecOption (schema.fields.get position).codec
        (countingModel.storageNbt? (macroParameterPath source position) storage) :=
  countingModel_lawful.macroFieldStorage source storage position

private theorem score_set
    (scores : Scores) (target : Score) (value : Int32) :
    (evalCommand (mode := .plain) countingModel emptyCode 1 ()
        ⟨scores, fun _ => 0, #[]⟩
        (.scoreboard (.set target value))).map
      (fun result => (result.state.scores target, result.flow.outcome)) =
      some (value, .succeeded value) := by
  simp [evalCommand, countingModel, scoreResult, State.applyScore, updateScore,
    Flow.outcome]

private theorem score_set_reads_back
    (scores : Scores) (target : Score) (value : Int32) :
    updateScore scores target value target = value := by
  simp [updateScore]

private theorem score_get
    (scores : Scores) (target : Score) :
    (evalCommand (mode := .plain) countingModel emptyCode 1 ()
        ⟨scores, fun _ => 0, #[]⟩
        (.scoreboard (.get target))).map (fun result => result.flow.outcome) =
      some (.succeeded (scores target)) := by
  rfl

private theorem score_add
    (scores : Scores) (target source : Score) :
    (scoreResult (.operation target .add source) scores).outcome.result =
      scores target + scores source :=
  rfl

private theorem exact_condition
    (scores : Scores) (target : Score) :
    scoreCondition
      (.matches target (.between (scores target) (scores target) (by simp))) scores = true := by
  simp [scoreCondition, Oria.Target.DP121.Semantics.IntRange.contains]

private theorem nested_stores_execute_leaf_once
    (scores : Scores) (source success result : Score)
    (different : success ≠ result) :
    let command : Command .plain :=
      (({ success := some success, result := some result } : Capture)).wrap (.scoreboard (.get source))
    let evaluated := evalCommand (mode := .plain) countingModel emptyCode 3 ()
      ⟨scores, fun _ => 0, #[]⟩ command
    let finalScores := updateScore
      (updateScore scores result (scores source)) success 1
    evaluated.map (fun evaluatedResult =>
      (evaluatedResult.state.trace.size, evaluatedResult.state.scores success,
        evaluatedResult.state.scores result)) = some (1, 1, scores source) ∧
      finalScores success = 1 ∧ finalScores result = scores source := by
  simp [Capture.wrap, evalCommand, countingModel, scoreResult,
    State.applyScore, State.store, StoreKind.value, updateScore,
    Flow.outcome, Outcome.succeeded, Ne.symm different]
  change (Array.append (#[] : Array Nat) #[0]).size = 1
  decide

theorem macro_decode_failure {schema : MacroSchema}
    (model : Model)
    (code : Code)
    (callee : FunctionRef (.macro schema))
    (source : MacroSource schema)
    (mode : Mode)
    (env : ModeEnv mode)
    (state : State model)
    (failed : model.decodeMacro source state.storage = none) :
    evalCommand (mode := mode) model code 1 env state
        (.functionWithStorage callee source) =
      some ⟨state, .next .failed⟩ := by
  simp [evalCommand, failed]

private theorem plain_function_return
    (callee : FunctionRef .plain)
    (state : State countingModel) :
    let code : Code := ⟨fun {kind} _ => match kind with
      | .plain => .plain #[.returnValue 7]
      | .macro _ => .macro #[]⟩
    evalCommand (mode := .plain) countingModel code 4 () state (.function callee) =
      some ⟨state, .next (.succeeded 7)⟩ := by
  simp [evalCommand, evalBody, evalPlainLines, Flow.outcome]

private theorem macro_function_body_return
    (schema : MacroSchema)
    (env : MacroEnv schema)
    (state : State countingModel) :
    evalBody (kind := .macro schema) countingModel emptyCode 3 env state
        (.macro #[.static (.returnValue 9)]) =
      some ⟨state, .next (.succeeded 9)⟩ := by
  simp [evalBody, evalMacroLines, evalCommand]

end Oria.Proofs.DP121Semantics
