module

public import Oria.Compiler.Lower.DP121.Emit
public import Oria.Compiler.Lower.DP121.Memory

namespace Oria.Lower.DP121.Command

open Oria.Target.DP121

private def normalize (fragment : Oria.Command.Fragment (fun _ => Transfer.Source Place)) :
    Oria.Command.Fragment (fun _ => Transfer.Source Place) :=
  { fragment with segments := fragment.segments.map fun segment => match segment with
      | .hole .i32 (.imm value) => .i32 value
      | segment => segment }

private def argument {a : ObjTy} {k : Nat} (config : Config) (bank : Layout k)
    (path : String) (target : Place) :
    Oria.Command.HoleCodec a → Transfer.Source Place → Except Diagnostic Emitted
  | .i32, source => pure ⟨[Stack.move ⟨target, source⟩], []⟩
  | .nativeNbt, source => Memory.project config bank path source
      [([.key ⟨"value"⟩], target)] .either

/-- Prepare one macro compound for a body whose lines share the same typed parameters. -/
public def macroBody {schema : MacroSchema} {k : Nat} (config : Config) (bank : Layout k) (path : String)
    (sources : InvocationSources (fun _ => Transfer.Source Place) schema)
    (body : Array (FunctionLine schema)) : Except Diagnostic Emitted := do
  let storage ← config.runtime
  let helper : FunctionRef (.macro schema) := .ofId (← config.function path).id
  let arguments ← (List.finRange schema.fields.length).mapM fun i =>
    let target : Place := .storage
      ⟨storage, (Nbt.Path.key "macro").child (.key (schema.parameterKey i))⟩
    argument config bank (path ++ s!"/arg{i.val}") target (schema.fields.get i).codec (sources.get i)
  let source : MacroSource schema := ⟨storage, some (.key "macro")⟩
  pure ⟨arguments.flatMap (·.commands) ++ [.functionWithStorage helper source],
    [⟨.macro schema, ⟨helper, .macro body⟩⟩] ++
      arguments.flatMap (·.helpers)⟩

/-- Normalize immediate holes before assigning a native fragment's macro scope. -/
public def plan (value : Oria.Command.Fragment (fun _ => Transfer.Source Place)) :
    Except Diagnostic (FragmentPlan (fun _ => Transfer.Source Place)) :=
  planFragment (normalize value)

public def emit {sig : Oria.Command.Signature} {k : Nat} (config : Config) (bank : Layout k)
    (catalog : Oria.Command.Catalog)
    (path : String) (request : Oria.Command.Call (fun _ => Transfer.Source Place) sig) :
    Except Diagnostic Emitted := do
  let request := { request with args := request.args.map fun arg =>
    { arg with fragment := normalize arg.fragment } }
  let plan ← planWithCatalog catalog request
  plan.withInvocation
    (fun invocation => pure ⟨[.invoke invocation], []⟩)
    (fun schema nonempty sources invocation complete => do
      let command : Command (.macro schema) := .returnRun (.invoke invocation)
      have used : 0 < command.parameterCount := by
        change 0 < invocation.parameterCount
        rw [complete]
        exact nonempty
      macroBody config bank path sources #[.macro (.ofCommand command used)])

/-- Plan compiler-generated native syntax with the shared hole and macro machinery.
An explicit completion value distinguishes an executed false condition from macro parse failure. -/
public def fragment {k : Nat} (config : Config) (bank : Layout k) (path : String)
    (value : Oria.Command.Fragment (fun _ => Transfer.Source Place))
    (capture : Capture := {})
    (completion : Option Int32 := none)
    (temporaries : TemporaryEffect := .unknown) : Except Diagnostic Emitted := do
  let plan ← plan value
  plan.withInvocation
    (fun invocation => do
      let command := capture.wrap (.native ((invocation.withCost 4).withTemporaries temporaries))
      match completion with
      | none => pure ⟨[command], []⟩
      | some result =>
          let helper ← config.function path
          pure ⟨[.function helper], [⟨.plain, ⟨helper, .plain #[command, .returnValue result]⟩⟩]⟩)
    (fun _ nonempty sources invocation complete => do
      let command := capture.wrap (Command.native ((invocation.withCost 4).withTemporaries temporaries))
      have used : 0 < command.parameterCount := by
        simpa only [command, Capture.parameterCount_wrap, Command.parameterCount,
          FragmentInvocation.parameterCount_withTemporaries,
          FragmentInvocation.parameterCount_withCost, complete] using nonempty
      match completion with
      | none => macroBody config bank path sources #[.macro (.ofCommand (.returnRun command) used)]
      | some result =>
          macroBody config bank path sources #[.macro (.ofCommand command used), .static (.returnValue result)])

/-- A scoped macro returns after the complete native traversal. -/
public def execute {k : Nat} (config : Config) (bank : Layout k) (path : String)
    (chain : Oria.Command.Fragment (fun _ => Transfer.Source Place))
    (body : FunctionRef .plain) : Except Diagnostic Emitted := do
  let plan ← plan chain
  plan.withInvocation
    (fun invocation => pure ⟨[.execute invocation body], []⟩)
    (fun schema nonempty sources invocation complete => do
      let command : Command (.macro schema) := .execute invocation body
      have used : 0 < command.parameterCount := by
        change 0 < invocation.parameterCount
        rw [complete]
        exact nonempty
      macroBody config bank path sources #[.macro (.ofCommand command used), .static (.returnValue 0)])

/-- Capture only demanded native channels, publishing stack results after invocation. -/
public def capture {k : Nat} (bank : Layout k) (targets : Vector (Option Place) 2)
    (emitted : Emitted) : Except Diagnostic Emitted := do
  let channel (index : Fin 2) : Option Score := (targets.get index).map fun target =>
    match target with
    | .score score => score
    | .storage _ => bank.scratch[2 + index.val]
  let success := channel 0
  let result := channel 1
  let capture : Capture := ⟨success, result⟩
  let initial := (success.toList ++ result.toList).map fun score => Command.scoreboard (.set score 0)
  let after := (List.finRange 2).filterMap fun i => do
    let .storage target ← targets.get i | none
    let source ← channel i
    pure (Stack.move ⟨.storage target, .loc (.score source)⟩)
  match emitted.commands.reverse with
  | [] => throw (.unsupportedMachineLowering .anonymous)
  | command :: before =>
      pure { emitted with commands := before.reverse ++ initial ++ [capture.wrap command] ++ after }

/-- A multi-step native helper reads ordinary input homes until it returns. Capture in
reserved scratch registers, then publish demanded results to their allocated homes. -/
public def captureAfter {k : Nat} (bank : Layout k) (targets : Vector (Option Place) 2)
    (emitted : Emitted) : Except Diagnostic Emitted := do
  let temporary := Vector.ofFn fun i : Fin 2 =>
    targets[i].map fun _ => Place.score bank.scratch[2 + i.val]
  let emitted ← capture bank temporary emitted
  let after := (List.finRange 2).filterMap fun i => do
    let target ← targets[i]
    let source ← temporary[i]
    pure (Stack.move ⟨target, .loc source⟩)
  return { emitted with commands := emitted.commands ++ after }

end Oria.Lower.DP121.Command
