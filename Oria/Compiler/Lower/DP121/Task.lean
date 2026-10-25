module

public import Oria.Compiler.Lower.DP121.Values
public import Oria.Compiler.Analysis.Suspension
import Oria.Compiler.Lower.DP121.Cost
import Oria.Compiler.Lower.DP121.Arithmetic
import Oria.Compiler.Lower.DP121.Phase
import Oria.Nbt.Syntax

namespace Oria.Lower.DP121.Task

open Oria.IR Oria.Target.DP121 Oria.Datapack

variable {s : Oria.Program.ClosedProgram} {p : Machine.Program s} {k : Nat}

public abbrev Member (p : Machine.Program s) := Fin (Machine.signatures p.table s).length

public abbrev Emitter (p : Machine.Program s) :=
  {n m : Nat} → (i : Member p) → Fin (p.definitionAt i).layout.length → Nat →
    Machine.Op (Machine.signatures p.table s) n m → Except Diagnostic Emitted

private structure Point (p : Machine.Program s) where
  member : Member p
  block : Fin (p.definitionAt member).layout.length
  offset : Nat

private def Point.key (x : Point p) : Nat × Nat × Nat :=
  (x.member.val, x.block.val, x.offset)

private structure Site (p : Machine.Program s) where
  point : Point p
  {scope : Nat}
  body : Machine.Body (Machine.signatures p.table s) (p.definitionAt point.member).layout
    ((Machine.signatures p.table s).get point.member).result scope
  boundary : Bool

private def sites {n : Nat} (known : Vector Bool (Machine.signatures p.table s).length)
    (i : Member p) (b : Fin (p.definitionAt i).layout.length) (offset : Nat) (start boundary : Bool)
    (body : Machine.Body (Machine.signatures p.table s) (p.definitionAt i).layout
      ((Machine.signatures p.table s).get i).result n) : List (Site p) :=
  let head := if start then [⟨⟨i, b, offset⟩, body, boundary⟩] else []
  head ++ match body with
    | .done _ => []
    | .step op next =>
        let split := match op with | .checkpoint _ => true | .call f _ => known[f.index] | _ => false
        sites known i b (offset + 1) split true next

private structure Context (p : Machine.Program s) (k : Nat) where
  physical : Calling.Context p k
  known : Vector Bool (Machine.signatures p.table s).length
  all : Array (Site p)
  ids : Std.HashMap (Nat × Nat × Nat) Nat
  emit : Emitter p

private def score (c : Context p k) (name : Oria.Command.SyntaxToken) : Score :=
  ⟨.ofToken name, c.physical.config.objective⟩

private def location (c : Context p k) (key : String) : StoragePath :=
  ⟨c.physical.storage, .key key⟩

private def frame (c : Context p k) (key : String) : StoragePath :=
  ⟨c.physical.storage, ⟨.key ⟨"stack"⟩, [.index (-1), .key ⟨key⟩]⟩⟩

private def ref (c : Context p k) (name : String) : Except Diagnostic (FunctionRef .plain) :=
  c.physical.config.function ("__oria/task/" ++ name)

private def pointRef (c : Context p k) (x : Point p) (role : String) :=
  ref c s!"{role}/{x.member.val}/{x.block.val}/{x.offset}"

private def id (c : Context p k) (x : Point p) : Except Diagnostic Nat := do
  let some n := c.ids.get? x.key | throw (.invalidTask "missing continuation")
  return n

private def definition (target : FunctionRef .plain) (body : List (Command .plain)) : PackedFunction :=
  ⟨.plain, ⟨target, .plain body.toArray⟩⟩

private def amount (n : Nat) : Except Diagnostic {x : Int32 // 0 ≤ x} := do
  if n > 2147483647 then throw (.invalidTask "task amount exceeds I32")
  let x := Int32.ofNat n
  if h : 0 ≤ x then return ⟨x, h⟩ else throw (.invalidTask "negative task amount")

private def live {n : Nat} (c : Context p k) (x : Point p)
    (body : Machine.Body (Machine.signatures p.table s) (p.definitionAt x.member).layout
      ((Machine.signatures p.table s).get x.member).result n) : Except Diagnostic (BitVec n) :=
  match body with
  | .step _ _ =>
      if let some pt := (c.physical.plan.functions.get x.member |>.blocks.get x.block).info.points[x.offset]? then
        if h : pt.scope = n then pure (h ▸ (pt.inputs ||| pt.across))
        else throw (.invalidTask "suspension scope does not match liveness")
      else throw (.invalidTask "missing suspension liveness")
  | .done exit => pure (Analysis.Demand.terminatorUses
      (Analysis.Demand.functionInfo p c.physical.plan.demand x.member) exit)

private def registers {n : Nat} (c : Context p k) (x : Point p) (mask : BitVec n) :
    Except Diagnostic (List Score) := do
  (List.finRange n).filterMapM fun j => do
    if !mask.getLsb j then return none
    match ← Values.position c.physical x.member x.block (Analysis.Machine.number j) .current with
    | some (.score s) => return some s
    | _ => return none

private def save (c : Context p k) (regs : List Score) : List (Command .plain) :=
  .data (.setValue (frame c "registers") (nbt% $(Array.replicate regs.length (0 : Int32)))) ::
    regs.zipIdx.map (fun (r, i) => Stack.move ⟨.storage { frame c "registers" with
      path := (frame c "registers").path.at i }, .loc (.score r)⟩)

private def restore (c : Context p k) (regs : List Score) : List (Command .plain) :=
  regs.zipIdx.map (fun (r, i) => Stack.move ⟨.score r, .loc (.storage { frame c "registers" with
    path := (frame c "registers").path.at i })⟩)

private def stop (c : Context p k) (status : Int32) : List (Command .plain) :=
  [Command.scoreboard (.set (score c "#task.status") status),
    .scoreboard (.set (score c "#task.phase") 0)] ++
    Heap.finish ⟨c.physical.storage, c.physical.config.objective⟩ ++ Stack.finish c.physical.storage ++
    (["results", "cursor", "memory_arg", "memory_object", "memory_draft", "memory_value",
      "memo", "memo_entry", "promotion", "promote_frame"].map fun key => Command.data (.remove (location c key))) ++
    [Phase.leave c.physical.config.objective, .returnValue 0]

private def orderedRouter (c : Context p k) (name : String)
    (entries : List (Nat × FunctionRef .plain)) : Except Diagnostic (List PackedFunction) := do
  let target ← ref c name
  match entries with
  | [] => return [definition target (stop c 3)]
  | [(n, f)] => return [definition target [
      .when .positive (.matches (score c "#task.pc") (.exact (Int32.ofNat n))) (.returnRun (.function f)),
      .returnRun (.function (← ref c "invalid"))]]
  | a :: b :: rest =>
      let entries := a :: b :: rest
      let mid := entries.length / 2
      let left := entries.take mid
      let right := entries.drop mid
      let pivot := (left.getLast?).map (·.1) |>.getD 0
      let l ← ref c (name ++ "/left")
      let r ← ref c (name ++ "/right")
      return definition target [
        .when .positive (.matches (score c "#task.pc") (.atMost (Int32.ofNat pivot))) (.returnRun (.function l)),
        .returnRun (.function r)] :: ((← orderedRouter c (name ++ "/left") left) ++
        (← orderedRouter c (name ++ "/right") right))
termination_by entries.length
decreasing_by all_goals simp_wf; omega

private def router (c : Context p k) (name : String)
    (entries : List (Nat × FunctionRef .plain)) : Except Diagnostic (List PackedFunction) :=
  orderedRouter c name (entries.mergeSort (fun a b => a.1 ≤ b.1))

private def edge {n : Nat} (c : Context p k) (x : Point p)
    (e : Machine.Edge (p.definitionAt x.member).layout n) : Except Diagnostic (List (Command .plain)) := do
  let destinations ← Values.parameters c.physical x.member e.target.index
  let moves ← Values.copies c.physical x.member x.block .current
    (e.target.typeCorrect ▸ destinations) e.values
  return (← Stack.parallel c.physical.bank moves) ++
    [.returnRun (.function (← pointRef c ⟨x.member, e.target.index, 0⟩ "body"))]

private def exit {n : Nat} (c : Context p k) (x : Point p) :
    Machine.Terminator (p.definitionAt x.member).layout
      ((Machine.signatures p.table s).get x.member).result n → Except Diagnostic Emitted
  | .ret values => do
      let mask := (Analysis.Demand.functionInfo p c.physical.plan.demand x.member).result
      let outs := Vector.ofFn fun j : Fin values.size =>
        if mask.getLsb j then some (Place.storage { location c "results" with
          path := (location c "results").path.at j.val }) else none
      let writes ← Values.copies c.physical x.member x.block .current outs values
      let returner ← ref c "returned"
      let flag := score c "#task.result"
      let canFail := s.members[Machine.memberPosition p.table s x.member].signature.grade.canFail
      return ⟨[.data (.setValue (location c "results") (nbt% $(Array.replicate values.size (0 : Int32))))] ++
        writes.map Stack.move ++ [
          .scoreboard (.set flag 1)] ++
        (if canFail then [Stack.move ⟨.score flag, .loc (.storage
          { location c "results" with path := (location c "results").path.at 0 })⟩] else []) ++
        Stack.pop c.physical.storage ++ [.returnRun (.function returner)], []⟩
  | .jump e => return ⟨← edge c x e, []⟩
  | .branch cond yes no => do
      let condition ← cond.traverse (Values.operand c.physical x.member x.block .current)
      let (before, test) := Arithmetic.condition c.physical.bank condition
      let a ← helper 0 yes
      let b ← helper 1 no
      return ⟨before ++ [.when .positive test (.returnRun (.function a.1)),
        .returnRun (.function b.1)], a.2 ++ b.2⟩
  | .switch value cases fallback => do
      let value ← Values.operand c.physical x.member x.block .current value
      let (before, src) := Arithmetic.operand c.physical.bank.scratch[0] value
      let branches : List (Command .plain × List PackedFunction) ← cases.zipIdx.mapM fun ((tag, e), i) => do
        let f ← helper i e
        return (Command.when .positive (.matches src (.exact tag)) (.returnRun (.function f.1)), f.2)
      let last : Command .plain × List PackedFunction ← match fallback with
        | none => pure (Command.returnRun (.function (← ref c "invalid")), [])
        | some e => do
            let f ← helper cases.length e
            pure (Command.returnRun (.function f.1), f.2)
      return ⟨before ++ branches.map (·.1) ++ [last.1], branches.flatMap (·.2) ++ last.2⟩
where
  helper {n : Nat} (index : Nat) (e : Machine.Edge (p.definitionAt x.member).layout n) :
      Except Diagnostic (FunctionRef .plain × List PackedFunction) := do
    let target ← pointRef c x s!"edge{index}"
    return (target, [definition target (← edge c x e)])

private def emit {n : Nat} (c : Context p k) (x : Point p) :
    Machine.Body (Machine.signatures p.table s) (p.definitionAt x.member).layout
      ((Machine.signatures p.table s).get x.member).result n →
    Except Diagnostic (Emitted × List (Nat × FunctionRef .plain))
  | .done value => return (← exit c x value, [])
  | .step op next => match op with
    | .checkpoint forced => do
      let y : Point p := { x with offset := x.offset + 1 }
      return (⟨[.returnRun (.function (← pointRef c y (if forced then "park" else "gate")))], []⟩, [])
    | .call (sig := sig) f args => do
      if !c.known[f.index] then
        let op ← c.emit x.member x.block x.offset (.call f args)
        let (rest, landings) ← emit c { x with offset := x.offset + 1 } next
        return (⟨op.commands ++ rest.commands, op.helpers ++ rest.helpers⟩, landings)
      let y : Point p := { x with offset := x.offset + 1 }
      let nextId ← id c y
      let block := c.physical.plan.functions.get x.member |>.blocks.get x.block
      let some pt := block.info.points[x.offset]? | throw (.invalidTask "missing call liveness")
      let mask : BitVec n ← if h : pt.scope = n then pure (h ▸ pt.across)
        else throw (.invalidTask "call scope does not match liveness")
      let regs ← registers c x mask
      let defn := p.definitionAt f.index
      let parameters ← Values.parameters c.physical f.index defn.entry.index
      let params := f.typeCorrect ▸ (defn.entry.typeCorrect ▸ parameters)
      let moves ← Values.copies c.physical x.member x.block .caller params args
      let stack := moves.filter (fun m => match m.target with | .storage _ => true | _ => false)
      let rs := moves.filter (fun m => match m.target with | .score _ => true | _ => false)
      let inputs ← Stack.parallel c.physical.bank rs
      let child := c.physical.plan.functions.get f.index
      let goto ← pointRef c ⟨f.index, defn.entry.index, 0⟩ "body"
      let landing ← pointRef c y "landing"
      let outs ← Values.targets c.physical x.member x.block n sig.result .current
      let imports := outs.toList.zipIdx.filterMap fun (target, i) => target.map fun target =>
        Stack.move ⟨target, .loc (.storage { location c "results" with
          path := (location c "results").path.at i })⟩
      let landed := restore c regs ++ imports ++ [.returnRun (.function (← pointRef c y "gate"))]
      let commands := save c regs ++ [.data (.setValue (frame c "return") (.int (Int32.ofNat nextId)))] ++
        Stack.push c.physical.storage ⟨child.slots, 0, 0⟩ ++ stack.map Stack.move ++ inputs ++
        [.returnRun (.function goto)]
      return (⟨commands, [definition landing landed]⟩, [(nextId, landing)])
    | op => do
      let op ← c.emit x.member x.block x.offset op
      let (rest, landings) ← emit c { x with offset := x.offset + 1 } next
      return (⟨op.commands ++ rest.commands, op.helpers ++ rest.helpers⟩, landings)

public structure Generated where
  functions : List PackedFunction
  starts : Std.HashMap Nat (FunctionRef .plain)
  load : List (Command .plain)

/-- Compile one controlled server task workspace. Coroutine frames retain call continuations;
only register words live at a parked boundary are copied, and the arena stays resident. -/
public def generate (physical : Calling.Context p k) (known : Vector Bool (Machine.signatures p.table s).length)
    (emitOp : Emitter p) (sync : List PackedFunction) (roots : List (Member p)) : Except Diagnostic Generated := do
  let all := ((List.finRange (Machine.signatures p.table s).length).flatMap fun i =>
    if known[i] then (List.finRange (p.definitionAt i).layout.length).flatMap fun b =>
      sites known i b 0 true (b == (p.definitionAt i).entry.index) ((p.definitionAt i).blocks.get b)
    else []).toArray
  let ids := Std.HashMap.ofList (all.toList.zipIdx.map (fun (site, i) => (site.point.key, i + 1)))
  let c : Context p k := ⟨physical, known, all, ids, emitOp⟩
  let mut functions := sync
  let mut boundaries : Std.HashSet String := {}
  let mut gates : List (FunctionRef .plain × FunctionRef .plain × FunctionRef .plain) := []
  let mut resumed : List (Nat × FunctionRef .plain) := []
  let mut landings : List (Nat × FunctionRef .plain) := []
  let wake ← ref c "resume"
  let invalid ← ref c "invalid"
  let completed ← ref c "completed"
  let failed ← ref c "failed"
  functions := functions ++ [definition invalid (stop c 3), definition completed (stop c 2),
    definition failed (stop c 3), definition (← ref c "cancel") (stop c 5)]
  for site in all do
    let x := site.point
    let (emitted, returns) ← emit c x site.body
    let work ← pointRef c x "work"
    let entry ← pointRef c x "body"
    functions := functions ++ definition work emitted.commands :: emitted.helpers
    landings := landings ++ returns
    if !site.boundary then
      functions := functions ++ [definition entry [.returnRun (.function work)]]
      continue
    let gate ← pointRef c x "gate"
    let park ← pointRef c x "park"
    let restoreFn ← pointRef c x "restore"
    let regs ← registers c x (← live c x site.body)
    let n ← id c x
    let cursor := score c "#heap_count"
    functions := functions ++ [
      definition entry [.returnRun (.function gate)],
      definition park (save c regs ++ [
        Stack.move ⟨.storage (location c "cursor"), .loc (.score cursor)⟩,
        .scoreboard (.set (score c "#task.pc") (Int32.ofNat n)),
        .scoreboard (.set (score c "#task.phase") 1),
        .scoreboard (.add (score c "#task.parks") 1 (by decide)),
        Phase.leave physical.config.objective, .schedule wake, .returnValue 0]),
      definition restoreFn (restore c regs ++ [
        Stack.move ⟨.score cursor, .loc (.storage (location c "cursor"))⟩,
        .returnRun (.function gate)])]
    boundaries := boundaries.insert gate.id.render
    gates := gates ++ [(gate, work, park)]
    resumed := resumed ++ [(n, restoreFn)]
  let hasParent := score c "#task.parent"
  let pc := score c "#task.pc"
  let ret ← ref c "returned"
  let returnRouter ← ref c "return"
  functions := functions ++ (← router c "return" landings) ++ [definition ret [
    .store .success (.score hasParent) (.data (.get (frame c "return"))),
    .when .positive (.matches hasParent (.exact 1))
      (.store .result (.score pc) (.data (.get (frame c "return")))),
    .when .positive (.matches hasParent (.exact 1)) (.returnRun (.function returnRouter)),
    .when .negative (.matches (score c "#task.result") (.exact 1)) (.returnRun (.function failed)),
    .returnRun (.function completed)]]
  let dispatch ← ref c "dispatch"
  let mut starts : Std.HashMap Nat (FunctionRef .plain) := {}
  for root in roots.eraseDups do
    let start ← ref c s!"start/{root.val}"
    let initial ← ref c s!"initial/{root.val}"
    let plan := physical.plan.functions.get root
    let arena := physical.resources[root].arena
    let heap : Heap.Config := ⟨physical.storage, physical.config.objective⟩
    let n := all.size + root.val + 1
    let execute ← if known[root] then do
      let first := (p.definitionAt root).entry.index
      pure [Command.returnRun (.function (← pointRef c ⟨root, first, 0⟩ "body"))]
      else do
        let outputs ← if s.members[Machine.memberPosition p.table s root].signature.grade.canFail then do
          let some (some result) := plan.returns.toArray[0]? | throw (.invalidTask "missing task failure exit")
          pure [⟨Place.score (score c "#task.result"), .loc (Calling.resultPlace physical result)⟩]
          else pure []
        pure ([Command.scoreboard (.set (score c "#task.result") 1)] ++
          (← Calling.invoke physical root #[] (fun _ => pure []) (fun _ => pure outputs)) ++
          [.when .negative (.matches (score c "#task.result") (.exact 1)) (.returnRun (.function failed)),
            .returnRun (.function completed)])
    let work ← ref c s!"initial-work/{root.val}"
    let park ← ref c s!"initial-park/{root.val}"
    functions := functions ++ [definition work execute,
      definition park [.scoreboard (.set pc (Int32.ofNat n)), .scoreboard (.set (score c "#task.phase") 1),
        Phase.leave physical.config.objective, .schedule wake, .returnValue 0],
      definition start ([Phase.guard physical.config.objective,
        .when .positive (.matches (score c "#task.phase") (.atLeast 1)) .returnFail,
        Phase.set physical.config.objective .entry,
        .scoreboard (.set (score c "#task.status") 1), .scoreboard (.set (score c "#task.parks") 0),
        .scoreboard (.set (score c "#task.owner") (Int32.ofNat root.val)),
        .scoreboard (.set (score c "#task.slices") 0), .scoreboard (.set (score c "#task.phase") 1),
        .scoreboard (.set pc (Int32.ofNat n))] ++ (if arena then Heap.begin heap else []) ++
        Stack.begin physical.storage ++ Stack.push physical.storage ⟨if known[root] then plan.slots else 0, 0, 0⟩ ++
        [.data (.setValue (location c "cursor") (.int 0)),
          Phase.leave physical.config.objective, .schedule wake, .returnValue 0])]
    boundaries := boundaries.insert initial.id.render
    gates := gates ++ [(initial, work, park)]
    resumed := resumed ++ [(n, initial)]
    starts := starts.insert root.val start
  functions := functions ++ (← router c "dispatch" resumed)
  let mut required := 0
  let mut reserve := 0
  let mut charges := []
  for (gate, work, park) in gates do
    let cost ← Cost.bound functions.toArray boundaries work
    let parking ← Cost.bound functions.toArray boundaries park
    let charge := cost + 4
    required := max required charge
    reserve := max reserve (parking + 2)
    charges := charges ++ [(gate, work, park, charge)]
  let cap := score c "#task.cap"
  let fuel := score c "#task.fuel"
  let tooSmall ← ref c "budget-error"
  functions := functions ++ [definition tooSmall (stop c 4)]
  let draft := definition wake [
    Phase.guard physical.config.objective,
    .when .negative (.matches (score c "#task.phase") (.exact 1)) (.returnValue 0),
    Phase.set physical.config.objective .task,
    .store .result (.score cap) .commandLimit,
    .when .negative (.matches cap (.atLeast 1)) (.returnRun (.function tooSmall)),
    .scoreboard (.set fuel 0), .scoreboard (.operation fuel .minimum cap),
    .scoreboard (.remove fuel 0 (by decide)),
    .scoreboard (.set (score c "#task.phase") 2),
    .scoreboard (.add (score c "#task.slices") 1 (by decide)),
    Stack.move ⟨.score (score c "#heap_count"), .loc (.storage (location c "cursor"))⟩,
    .returnRun (.function dispatch)]
  let bootstrap ← Cost.bound (functions ++ [draft]).toArray boundaries wake
  let margin := bootstrap + reserve
  if physical.config.sliceBudget < required + margin then
    throw (.taskBudgetTooSmall physical.config.sliceBudget (required + margin))
  if physical.config.sliceBudget > 2147483647 || required + margin > 2147483647 then
    throw (.invalidTask "task budget exceeds I32")
  for (gate, work, park, charge) in charges do
    let n ← amount charge
    functions := functions ++ [definition gate [
      .when .negative (.matches fuel (.atLeast (Int32.ofNat charge))) (.returnRun (.function park)),
      .scoreboard (.remove fuel n.val n.property),
      .returnRun (.function work)]]
  let marginWord ← amount margin
  functions := functions ++ [definition wake [
    Phase.guard physical.config.objective,
    .when .negative (.matches (score c "#task.phase") (.exact 1)) (.returnValue 0),
    Phase.set physical.config.objective .task,
    .store .result (.score cap) .commandLimit,
    .when .negative (.matches cap (.atLeast (Int32.ofNat (required + margin)))) (.returnRun (.function tooSmall)),
    .scoreboard (.set fuel (Int32.ofNat physical.config.sliceBudget)),
    .scoreboard (.operation fuel .minimum cap),
    .scoreboard (.remove fuel marginWord.val marginWord.property),
    .scoreboard (.set (score c "#task.phase") 2),
    .scoreboard (.add (score c "#task.slices") 1 (by decide)),
    Stack.move ⟨.score (score c "#heap_count"), .loc (.storage (location c "cursor"))⟩,
    .returnRun (.function dispatch)]]
  return ⟨functions, starts, (stop c 0).dropLast.dropLast⟩

end Oria.Lower.DP121.Task
