module

public import Oria.Compiler.Lower.DP121.Calling
import Oria.Compiler.Lower.DP121.Values
public import Oria.Compiler.Lower.DP121.Command
public import Oria.Compiler.Lower.DP121.Execute
import Oria.Compiler.Lower.DP121.Transfers
public import Oria.Compiler.Lower.DP121.Memory
public import Oria.Compiler.Lower.DP121.Nbt
public import Oria.Compiler.Lower.DP121.Persistent.Promote
public import Oria.Compiler.Lower.DP121.Persistent.Initialize
public import Oria.IR.Common.Json
import Oria.Compiler.Optimize.Sharing
import Oria.Compiler.Optimize.Linearize
import Oria.Compiler.Optimize.MacroArguments
import Oria.Compiler.Lower.DP121.Task
import Oria.Compiler.Lower.DP121.Phase
import Oria.Compiler.Lower.DP121.Globals

namespace Oria.Lower.DP121

open Oria.Datapack Oria.IR Oria.Target.DP121
open Values

variable {source : Oria.Program.ClosedProgram} {program : Machine.Program source} {k : Nat}

private def failureAt (_ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) : Diagnostic :=
  .invalidRegisterAllocation source.members[Machine.memberPosition program.table source i].source

private def rootPath (config : Config) (name : Lean.Name) : Except Diagnostic StoragePath := do
  let some id := config.rootNames.get? name | throw (.unknownRoot name)
  pure ⟨(← config.memory).storage, ⟨.key ⟨"roots"⟩, [.key ⟨id.text⟩]⟩⟩

private def emitEdge {n : Nat} (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (edge : Machine.Edge (program.definitionAt i).layout n) : Except Diagnostic Emitted := do
  let destinations ← parameters ctx i edge.target.index
  let moves ← copies ctx i b .current (edge.target.typeCorrect ▸ destinations) edge.values
  let commands ← Stack.parallel ctx.bank moves
  let target ← ctx.config.function s!"__oria/m{i.val}/b{edge.target.index.val}"
  pure ⟨commands ++ [.returnRun (.function target)], []⟩

private def emitExit {n : Nat} (ctx : Calling.Context program k)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length) :
    Machine.Terminator (program.definitionAt i).layout
      ((Machine.signatures program.table source).get i).result n → Except Diagnostic Emitted
  | .ret values => do
      let destinations := (ctx.plan.functions.get i).returns.map (Option.map (Calling.resultPlace ctx))
      let moves ← copies ctx i b .current destinations values
      pure ⟨(← Stack.parallel ctx.bank moves) ++ [.returnValue 0], []⟩
  | .jump edge => emitEdge ctx i b edge
  | .branch condition yes no => do
      let condition ← condition.traverse (operand ctx i b .current)
      let yes ← helper 0 yes
      let no ← helper 1 no
      let (before, test) := Arithmetic.condition ctx.bank condition
      pure ⟨before ++ [
        .when .positive test (.returnRun (.function yes.1)),
        .returnRun (.function no.1)], yes.2 ++ no.2⟩
  | .switch value cases fallback => do
      let value ← operand ctx i b .current value
      let (before, score) := Arithmetic.operand ctx.bank.scratch[0] value
      let cases : List (Command .plain × List PackedFunction) ← cases.zipIdx.mapM fun ((tag, edge), index) => do
        let (ref, functions) ← helper index edge
        pure (Command.when .positive (.matches score (.exact tag)) (.returnRun (.function ref)), functions)
      let (last, functions) : Command .plain × List PackedFunction ← match fallback with
        | none => pure (Command.returnFail, [])
        | some edge => do
            let (ref, functions) ← helper cases.length edge
            pure (.returnRun (.function ref), functions)
      pure ⟨before ++ cases.map (·.1) ++ [last], cases.flatMap (·.2) ++ functions⟩
where
  helper {n : Nat} (index : Nat) (edge : Machine.Edge (program.definitionAt i).layout n) :
      Except Diagnostic (FunctionRef .plain × List PackedFunction) := do
    let emitted ← emitEdge ctx i b edge
    match emitted.commands with
    | [.returnRun (.function target)] => pure (target, [])
    | _ => do
        let ref ← ctx.config.function s!"__oria/m{i.val}/b{b.val}/e{index}"
        pure (ref, [⟨.plain, ⟨ref, .plain emitted.commands.toArray⟩⟩])

private def emitOp {n m : Nat} (ctx : Calling.Context program k) (catalog : Oria.Command.Catalog)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (index : Nat) (op : Machine.Op (Machine.signatures program.table source) n m) :
    Except Diagnostic Emitted := do
      let out ← targets ctx i b n m .current
      let read := operand ctx i b .current
      let path := s!"__oria/m{i.val}/b{b.val}/i{index}"
      let emitted ← match op with
        | .division l r =>
            pure ⟨Arithmetic.division ctx.bank out (← read l) (← read r), []⟩
        | .checkpoint _ => throw (.invalidTask "suspension requires a Datapack.task entry")
        | .nbt operation args =>
            args.traverseK (fun value k => read value >>= k) fun values =>
              Nbt.emit ctx.config ctx.bank (path ++ "/nbt") operation values out
        | .unary op value => match out[0] with
            | none => pure ⟨[], []⟩
            | some target => pure ⟨Arithmetic.unary ctx.bank op target (← read value), []⟩
        | .binary op l r => match out[0] with
            | none => pure ⟨[], []⟩
            | some target => pure ⟨Arithmetic.binary ctx.bank op target (← read l) (← read r), []⟩
        | .call (sig := sig) callee args => do
            let defn := program.definitionAt callee.index
            let destinations ← parameters ctx callee.index defn.entry.index
            let destinations := callee.typeCorrect ▸ (defn.entry.typeCorrect ▸ destinations)
            let result := (ctx.plan.functions.get callee.index).returns.map
              (Option.map (Calling.resultPlace ctx))
            let result := callee.typeCorrect ▸ result
            let block := (ctx.plan.functions.get i).blocks.get b
            let some saved := block.saved[index]? | throw (failureAt ctx i)
            let commands ← Calling.invoke ctx callee.index saved
              (fun frame => copies ctx i b frame destinations args)
              (fun frame => do
                let destinations ← targets ctx i b n sig.result frame
                (destinations.zip result).toList.filterMapM fun (target, source) => do
                  match target with
                  | none => pure none
                  | some target =>
                      let some source := source | throw (failureAt ctx i)
                      pure (some ⟨target, .loc source⟩))
            pure ⟨commands, []⟩
        | .command request => do
            let request ← request.traverseK (fun value next => read value >>= next) pure
            let emitted ← Command.emit ctx.config ctx.bank catalog (path ++ "/macro") request
            Command.capture ctx.bank out emitted
        | .execute scope canFail callee args => do
            let defn := program.definitionAt callee.index
            let destinations ← parameters ctx callee.index defn.entry.index
            let destinations := cast
              (congrArg (fun sig : Machine.Signature => Vector (Option Place) sig.args) callee.typeCorrect)
              (defn.entry.typeCorrect ▸ destinations)
            let captures ← copies ctx i b .caller destinations args
            let block := (ctx.plan.functions.get i).blocks.get b
            let some saved := block.saved[index]? | throw (failureAt ctx i)
            let frame := if captures.isEmpty && saved.isEmpty then Stack.Frame.current else .caller
            let scope ← scope.traverseK
              (fun value next => operand ctx i b frame value >>= next) pure
            Execute.emit ctx path scope canFail callee saved captures
        | .allocate shape values => match out[0] with
            | none => pure ⟨[], []⟩
            | some target =>
                pure ⟨Heap.allocate ⟨ctx.storage, ctx.config.objective⟩ shape (← values.mapM read) target, []⟩
        | .tag value =>
            match out[0] with
            | none => pure ⟨[], []⟩
            | some target => do
                let value ← read value
                Memory.project ctx.config ctx.bank (path ++ "/read") value
                  [([.key ⟨"tag"⟩], target)]
                  (if program.persistent.nodeCount == 0 then .ephemeral else .either)
        | .project _ value => do
            let fields : List (List Nbt.PathSegment × Place) := out.toList.zipIdx.filterMap fun (target, offset) =>
              target.map fun target => ([Nbt.PathSegment.key ⟨"payload"⟩, .index offset], target)
            if fields.isEmpty then pure ⟨[], []⟩
            else
              let value ← read value
              Memory.project ctx.config ctx.bank (path ++ "/read") value fields
                (if program.persistent.nodeCount == 0 then .ephemeral else .either)
        | .promote type value => do
            let memory ← ctx.config.memory
            let some plan := program.persistent.lookup? type
              | throw (.unsupportedRepresentation .anonymous type .body)
            let target ← Persistent.Runtime.ref memory s!"copy/{plan.val}"
            let input := Persistent.Runtime.score memory "#p_source"
            let result := Persistent.Runtime.score memory "#p_result"
            let temporary (key : String) : StoragePath := ⟨memory.runtime, .key key⟩
            pure ⟨[
              .data (.setValue (temporary "memo") (.compound .nil)),
              .data (.setValue (temporary "promotion") (.list (.nil : Nbt.Values))),
              Stack.move ⟨.score input, ← read value⟩, .function target] ++
              (out[0].toList.map fun target => Stack.move ⟨target, .loc (.score result)⟩) ++
              (["memo", "promotion", "promote_frame", "memo_entry"].map fun key =>
                Command.data (.remove (temporary key))), []⟩
        | .rootGet root => do
            let location ← rootPath ctx.config root.name
            pure ⟨out.toList.zipIdx.filterMap (fun (target, offset) => target.map fun target =>
              Stack.move ⟨target, .loc (.storage { location with path := location.path.at offset })⟩), []⟩
        | .rootSet root values => do
            let location ← rootPath ctx.config root.name
            let values ← values.mapM read
            pure ⟨[.data (.setValue location (.list (.ofArray
              (Array.replicate values.size (.int 0)))))] ++
              values.toList.zipIdx.map (fun (value, offset) =>
                Stack.move ⟨.storage { location with path := location.path.at offset }, value⟩), []⟩
        | .refNew shape values => do
            let memory ← ctx.config.memory
            let draft : StoragePath := ⟨memory.runtime, .key "memory_draft"⟩
            let seed : Nbt.Value .compound := .compound
              (.cons ⟨"d"⟩ (.int (Int32.ofNat shape.scanCode))
                (.cons ⟨"tag"⟩ (.int shape.tag)
                  (.cons ⟨"payload"⟩ (.list (.ofArray (Array.replicate values.size (.int 0)))) .nil)))
            let fields ← (List.finRange values.size).mapM fun field => do
              pure (Stack.move ⟨.storage ⟨memory.runtime,
                ⟨.key ⟨"memory_draft"⟩, [.key ⟨"payload"⟩, .index field.val]⟩⟩, ← read values[field]⟩)
            let allocate ← Persistent.Runtime.ref memory "allocate"
            pure ⟨[.data (.setValue draft seed)] ++ fields ++ [.function allocate] ++
              (out[0].toList.map fun target => Stack.move
                ⟨target, .loc (.score (Persistent.Runtime.score memory "#p_result"))⟩), []⟩
        | .refGet _ value => do
            let fields : List (List Nbt.PathSegment × Place) := out.toList.zipIdx.filterMap fun (target, offset) =>
              target.map fun target => ([Nbt.PathSegment.key ⟨"payload"⟩, .index offset], target)
            if fields.isEmpty then
              let memory ← ctx.config.memory
              let (loaded, pointer) := Memory.operand ctx.bank (← read value)
              let ref : FunctionRef (.macro Heap.addressSchema) :=
                .ofId (← Persistent.Runtime.ref memory "read").id
              pure ⟨loaded ++ Persistent.Runtime.address memory pointer ++
                [.functionWithStorage ref (Persistent.Runtime.source memory)], []⟩
            else Memory.project ctx.config ctx.bank (path ++ "/read") (← read value) fields .persistent
        | .refSet _ cell values => do
            let memory ← ctx.config.memory
            let (loaded, pointer) := Memory.operand ctx.bank (← read cell)
            let valuePath : StoragePath := ⟨memory.runtime, .key "memory_value"⟩
            let fields ← (List.finRange values.size).mapM fun field => do
              pure (Stack.move ⟨.storage ⟨memory.runtime, valuePath.path.child (.index field.val)⟩,
                ← read values[field]⟩)
            let ref : FunctionRef (.macro Heap.addressSchema) := .ofId (← ctx.config.function (path ++ "/write")).id
            let command : Command (.macro Heap.addressSchema) :=
              .data (.setFrom (.index ⟨memory.storage, .key "slots"⟩
                ⟨0, by simp [Heap.addressSchema]⟩ [.key ⟨"payload"⟩]) valuePath)
            let helper : FunctionDef (.macro Heap.addressSchema) :=
              ⟨ref, .macro #[.macro (.ofCommand command (by
                simp [command, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]))]⟩
            pure ⟨[.data (.setValue valuePath
                (.list (.ofArray (Array.replicate values.size (.int 0)))))] ++ fields ++ loaded ++
              Persistent.Runtime.address memory pointer ++
              [.functionWithStorage ref (Persistent.Runtime.source memory), .data (.remove valuePath)],
              [⟨.macro Heap.addressSchema, helper⟩]⟩
      pure emitted

private def emitBody {n : Nat} (ctx : Calling.Context program k) (catalog : Oria.Command.Catalog)
    (i : Fin (Machine.signatures program.table source).length) (b : Fin (program.definitionAt i).layout.length)
    (index : Nat) :
    Machine.Body (Machine.signatures program.table source) (program.definitionAt i).layout
      ((Machine.signatures program.table source).get i).result n → Except Diagnostic Emitted
  | .done exit => emitExit ctx i b exit
  | .step op next => do
      let emitted ← emitOp ctx catalog i b index op
      let rest ← emitBody ctx catalog i b (index + 1) next
      pure ⟨emitted.commands ++ rest.commands, emitted.helpers ++ rest.helpers⟩

private def invoke (ctx : Calling.Context program k)
    (target : Fin (Machine.signatures program.table source).length)
    (results : Stack.Frame → Except Diagnostic (List (Transfer.Move Place)) := fun _ => pure []) :
    Except Diagnostic (List (Command .plain)) := do
  let commands ← Calling.invoke ctx target #[] (fun _ => pure []) results
  let stack := ctx.resources[target].stack
  pure ((if stack then Stack.begin ctx.storage else []) ++ commands ++
    (if stack then Stack.finish ctx.storage else []))

private def invokeEntry (ctx : Calling.Context program k) (memory : Bool)
    (target : Fin (Machine.signatures program.table source).length) (propagate : Bool := true) :
    Except Diagnostic (List (Command .plain)) := do
  let heap : Heap.Config := ⟨ctx.storage, ctx.config.objective⟩
  let usage := ctx.resources[target]
  let begin := if usage.arena then Heap.begin heap else []
  let keys := (if usage.arena then ["arena", "draft"] else []) ++
    (if usage.projection then ["heap_arg", "memory_arg"] else []) ++
    (if usage.nbt then ["nbt_input"] else []) ++
    (if usage.memory then ["memory_draft", "memory_object", "memory_arg", "memory_value",
      "memo", "promotion", "promote_frame", "memo_entry"] else [])
  let finish := keys.eraseDups.map (fun key => Command.data
      (.remove (⟨ctx.storage, .key key⟩ : StoragePath))) ++
    (if usage.macros then [.data (.setValue (⟨ctx.storage, .key "macro"⟩ : StoragePath) (.compound .nil))] else [])
  let canFail := source.members[Machine.memberPosition program.table source target].signature.grade.canFail
  let status : Score := ⟨.ofToken "#entry_success", ctx.config.objective⟩
  let commands ← invoke ctx target fun _ => do
    if !canFail || !propagate then return []
    let some (some result) := (ctx.plan.functions.get target).returns.toArray[0]?
      | throw (.unsupportedMachineLowering .anonymous)
    pure [⟨.score status, .loc (Calling.resultPlace ctx result)⟩]
  let failed := if canFail && propagate then
      [Command.when .negative (.matches status (.exact 1)) .returnFail] else []
  let run := [Phase.set ctx.config.objective .entry] ++ begin ++ commands ++ finish ++
    [Phase.leave ctx.config.objective]
  if !memory then return Phase.guard ctx.config.objective :: (run ++ failed)
  let persistent ← ctx.config.memory
  let ready := Persistent.Runtime.score persistent "#ready"
  let panic := Persistent.Runtime.score persistent "#panic"
  pure ([Phase.guard ctx.config.objective,
    .when .negative (.matches ready (.exact 1)) .returnFail,
    .scoreboard (.set panic 0)] ++ run ++
    [.when .positive (.matches panic (.exact 1)) .returnFail] ++ failed)

private def rootTarget (_ctx : Calling.Context program k) (requested : DeclRef.Some) :
    Except Diagnostic (Fin (Machine.signatures program.table source).length) := do
  let .named name := requested.ref.key
  let some position := source.position? name | throw (.unknownFunction name)
  let sig := source.members[position].signature
  unless sig == requested.sig do throw (.functionSignatureMismatch name requested.sig sig)
  pure (Machine.referenceAt program.table source position).index

private def entryFunctions (ctx : Calling.Context program k)
    (registrations : Array Registration)
    (tasks : Std.HashMap Nat (FunctionRef .plain) := {})
    (taskLoad : List (Command .plain) := [])
    (globalLoad : List (Command .plain) := []) : Except Diagnostic (List PackedFunction) := do
  let config := ctx.config
  let mut exports : Array PackedFunction := #[]
  let mut loads := []
  let mut ticks := []
  let managed := program.persistent.nodeCount != 0 || !config.collectors.isEmpty ||
    !source.collected.candidate.persistentRoots.isEmpty
  let memory := managed || !config.globals.isEmpty
  for r in registrations do
    let target ← rootTarget ctx r.reference
    if let .task path _ _ := r then
      let some start := tasks.get? target.val | throw (.invalidTask "missing task launcher")
      let ref : FunctionRef .plain := .ofId (.ofParts config.resourceNamespace path.val)
      let ready : List (Command .plain) := if memory then [Command.when .negative
        (.matches (⟨.ofToken "#ready", config.objective⟩ : Score) (.exact 1)) .returnFail] else []
      exports := exports.push ⟨.plain, ⟨ref, .plain (ready ++ [Command.returnRun (.function start)]).toArray⟩⟩
      let cancelPath ← (PublicFunctionPath.parse (path.render ++ "/cancel")).mapError
        (fun | .invalidResourceId text => .invalidResourceId text)
      let cancel : FunctionRef .plain := .ofId (.ofParts config.resourceNamespace cancelPath.val)
      let owner : Score := ⟨.ofToken "#task.owner", config.objective⟩
      let active : Score := ⟨.ofToken "#task.phase", config.objective⟩
      let cancelTarget ← (ResourcePath.parse "__oria/task/cancel").mapError
        (fun | .invalidResourceId text => .invalidResourceId text)
      let ns ← (ResourceNamespace.parse (config.resourceNamespace.render ++ ".task")).mapError
        (fun | .invalidResourceId text => .invalidResourceId text)
      exports := exports.push ⟨.plain, ⟨cancel, .plain #[
        Phase.guard config.objective,
        .when .negative (.matches active (.atLeast 1)) .returnFail,
        .when .negative (.matches owner (.exact (Int32.ofNat target.val))) .returnFail,
        Phase.set config.objective .entry,
        .returnRun (.function (.ofId (.ofParts ns cancelTarget)))]⟩⟩
      continue
    let commands ← invokeEntry ctx memory target (match r with | .entry .. => true | .hook .. | .task .. => false)
    match r with
    | .entry path _ =>
        let ref : FunctionRef .plain := .ofId (.ofParts config.resourceNamespace path.val)
        exports := exports.push ⟨.plain, ⟨ref, .plain (commands ++ [Command.returnValue 0]).toArray⟩⟩
    | .hook kind _ _ =>
        let ref ← config.function s!"__oria/hook/{exports.size}"
        exports := exports.push ⟨.plain, ⟨ref, .plain commands.toArray⟩⟩
        match kind with
        | .load => loads := loads ++ [Command.function ref]
        | .tick => ticks := ticks ++ [Command.function ref]
    | .task .. => pure ()
  for ⟨_, path, reference⟩ in config.collectors do
    let cfg ← config.memory
    let target ← rootTarget ctx ⟨_, reference⟩
    let ref : FunctionRef .plain := .ofId (.ofParts config.resourceNamespace path.val)
    let commands : List (Command .plain) := Phase.quiescent config.objective ++ [
      Command.when .negative (.matches (Persistent.Runtime.score cfg "#ready") (.exact 1)) .returnFail,
      Phase.set config.objective .collect,
      .scoreboard (.set (Persistent.Runtime.score cfg "#panic") 0)] ++ (← invoke ctx target) ++ [
      Phase.leave config.objective,
      .when .positive (.matches (Persistent.Runtime.score cfg "#panic") (.exact 1)) .returnFail,
      .returnValue 0]
    exports := exports.push ⟨.plain, ⟨ref, .plain commands.toArray⟩⟩
  let setup ← if managed then do
    let cfg ← config.memory
    pure [Command.function (← Persistent.Runtime.ref cfg "load")]
    else if memory then pure [Command.scoreboard (.set ⟨.ofToken "#ready", config.objective⟩ 1)]
    else pure []
  let ref ← config.function "__oria/load"
  let macroPath : StoragePath := ⟨ctx.storage, .key "macro"⟩
  let load : PackedFunction := ⟨.plain, ⟨ref, .plain (([
    Phase.guard config.objective,
    Command.scoreboard (.objectiveAdd config.objective),
    Phase.set config.objective .initialize,
    .data (.setValue macroPath (.compound .nil))] ++ setup ++ globalLoad ++ taskLoad ++
      [Phase.leave config.objective] ++ loads).toArray)⟩⟩
  if ticks.isEmpty then pure (load :: exports.toList)
  else
    let ref ← config.function "__oria/tick"
    pure (load :: ⟨.plain, ⟨ref, .plain ticks.toArray⟩⟩ :: exports.toList)

private def persistentFunctions (ctx : Calling.Context program k) :
    Except Diagnostic (List PackedFunction) := do
  if program.persistent.nodeCount == 0 && ctx.config.collectors.isEmpty &&
      source.collected.candidate.persistentRoots.isEmpty then return []
  let cfg ← ctx.config.memory
  let table := program.table
  let mut initializers : Array Persistent.Initialize.Root := #[]
  let mut wrappers : List PackedFunction := []
  let mut rootTypes : Array (ResourceId × ObjTy) := #[]
  for root in source.collected.candidate.persistentRoots do
    let some position := source.position? root.initial.source | throw (.unknownFunction root.initial.source)
    let i := (Machine.referenceAt program.table source position).index
    let path ← rootPath ctx.config root.ref.name
    let entry ← ctx.config.function s!"__oria/initializer/{i.val}"
    let results := (ctx.plan.functions.get i).returns
    let canFail := root.initial.signature.grade.canFail
    let status := Persistent.Runtime.score cfg "#initializer_success"
    let target := if canFail then (⟨cfg.runtime, .key "initial_result"⟩ : StoragePath) else path
    let commands ← invoke ctx i fun _ => results.toList.zipIdx.mapM fun (result, offset) => do
      let some result := result | throw (.unsupportedMachineLowering root.initial.source)
      let destination := if canFail && offset == 0 then Place.score status else
        .storage { target with path := target.path.at (offset - canFail.toNat) }
      pure ⟨destination, .loc (Calling.resultPlace ctx result)⟩
    let seed := Command.data (.setValue target
      (.list (.ofArray (Array.replicate (table.width root.initial.signature.result) (.int 0)))))
    let finish : List (Command .plain) := if canFail then [
        .when .positive (.matches status (.exact 1)) (.data (.setFrom path target)),
        .data (.remove target),
        .when .negative (.matches status (.exact 1)) .returnFail,
        .returnValue 0] else [.returnValue 0]
    wrappers := wrappers ++ [⟨.plain, ⟨entry, .plain ((seed :: commands) ++ finish).toArray⟩⟩]
    initializers := initializers.push ⟨entry⟩
    let some id := ctx.config.rootNames.get? root.ref.name | throw (.unknownRoot root.ref.name)
    rootTypes := rootTypes.push (id, root.initial.signature.result)
  let schema ← Persistent.Initialize.manifest table rootTypes
  let initFunctions ← Persistent.Initialize.generate cfg schema initializers
  let runtime ← Persistent.Runtime.generate cfg
  let promote ← Persistent.Promote.generate cfg program.persistent
  pure (wrappers ++ initFunctions ++ runtime ++ promote)

/-- Assign words once, then emit register/stack operations using the shared call protocol. -/
public def lower (config : Config) (program : Machine.Program source) (catalog : Oria.Command.Catalog)
    (registrations : Array Registration := #[]) : Except Diagnostic Target.DP121.Program := do
  if config.registerBudget < 6 then throw (.invalidRegisterBudget config.registerBudget)
  let k := config.registerBudget - 6
  let plan ← RegAlloc.build k program
  let bank ← Layout.allocate config.objective k
  let ctx : Calling.Context program k :=
    ⟨config, plan, bank, ← config.runtime, Resources.analyze program plan⟩
  let known := Analysis.Suspension.analyze program
  let roots ← registrations.toList.filterMapM fun registration => do
    if let .task _ _ _ := registration then return some (← rootTarget ctx registration.reference)
    let target ← rootTarget ctx registration.reference
    if known[target] then throw (.invalidTask "a suspending computation must be registered with Datapack.task")
    return none
  if registrations.isEmpty && known.toArray.any id then
    throw (.invalidTask "a suspending computation must be registered with Datapack.task")
  let mut taskStarts : Std.HashMap Nat (FunctionRef .plain) := {}
  let mut taskLoad := []
  let mut taskFunctions := []
  if !roots.isEmpty then
    let ns ← (ResourceNamespace.parse (config.resourceNamespace.render ++ ".task")).mapError
      (fun | .invalidResourceId text => .invalidResourceId text)
    let taskConfig := { config with resourceNamespace := ns }
    let taskCtx : Calling.Context program k := { ctx with config := taskConfig, storage := ← taskConfig.runtime }
    let mut sync := []
    for i in List.finRange (Machine.signatures program.table source).length do
      if known[i] then continue
      for b in List.finRange (program.definitionAt i).layout.length do
        let emitted ← emitBody taskCtx catalog i b 0 ((program.definitionAt i).blocks.get b)
        sync := sync ++ [⟨.plain, ⟨← taskConfig.function s!"__oria/m{i.val}/b{b.val}",
          .plain (Transfers.run emitted.commands).toArray⟩⟩] ++ emitted.helpers
    if program.persistent.nodeCount != 0 || !config.collectors.isEmpty ||
        !source.collected.candidate.persistentRoots.isEmpty then
      let memory ← taskConfig.memory
      sync := sync ++ (← Persistent.Runtime.generate memory) ++ (← Persistent.Promote.generate memory program.persistent)
    let task ← Task.generate taskCtx known (emitOp taskCtx catalog) sync roots
    taskStarts := task.starts
    taskLoad := task.load
    taskFunctions := task.functions
  let globals ← Globals.generate config
  let mut functions ← entryFunctions ctx registrations taskStarts taskLoad globals.commands
  functions := functions ++ globals.helpers
  functions := functions ++ (← persistentFunctions ctx)
  for i in List.finRange (Machine.signatures program.table source).length do
    if known[i] then continue
    for b in List.finRange (program.definitionAt i).layout.length do
      let emitted ← emitBody ctx catalog i b 0 ((program.definitionAt i).blocks.get b)
      let ref ← config.function s!"__oria/m{i.val}/b{b.val}"
      functions := functions ++ [⟨.plain, ⟨ref, .plain (Transfers.run emitted.commands).toArray⟩⟩] ++ emitted.helpers
  let shared := Optimize.Sharing.run (functions ++ taskFunctions).toArray
  let prepared := Optimize.MacroArguments.run ctx.storage (Optimize.Linearize.run shared)
  let complete := Optimize.Sharing.run prepared
  if unique : (complete.toList.map fun ⟨_, definition⟩ => definition.ref.id.render).Nodup then
    pure (.of complete unique)
  else throw (.invalidResourceId "generated DP121 function identities")

end Oria.Lower.DP121
