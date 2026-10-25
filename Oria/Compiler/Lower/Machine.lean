module

public import Oria.IR.Machine.Program
public import Oria.IR.Representation.Packing
import Oria.Compiler.Optimize.Machine
import Oria.Compiler.Optimize.Constants

namespace Oria.Lower.Machine

open Oria.IR
open Oria.Representation

variable {table : Table} {escaping : Bool}

private abbrev resultWidth (table : Table) (escaping : Bool) (a : ObjTy) :=
  if escaping then 1 + table.width a else table.width a

private def returned {n : Nat} {a : ObjTy} (escaping normal : Bool)
    (values : Vector (IR.Machine.Atom n) (table.width a)) :
    Vector (IR.Machine.Atom n) (resultWidth table escaping a) :=
  match escaping with
  | false => values
  | true => #v[IR.Machine.Atom.lit (n := n) (if normal then 1 else 0)] ++ values

private def unpackResult {n : Nat} {a : ObjTy} (flagged : Bool)
    (values : Vector (IR.Machine.Atom n) (resultWidth table flagged a)) :
    Option (IR.Machine.Atom n) × Vector (IR.Machine.Atom n) (table.width a) :=
  match flagged with
  | false => (none, values)
  | true => (some (values[0]'(by simp only [resultWidth, ite_true]; omega)),
      Vector.ofFn fun i => values[1 + i.val]'(by simp [resultWidth]))

private abbrev Frame (table : Table) (Γ : List ObjTy) (n : Nat) :=
  Args (fun a => Vector (IR.Machine.Atom n) (table.width a)) Γ

private def parameters : (Γ : List ObjTy) → Frame table Γ (table.arity Γ)
  | [] => .nil
  | a :: Γ =>
      .cons (Vector.ofFn fun i => .var ⟨i.val, by simp only [Table.arity]; omega⟩)
        ((parameters Γ).map fun values => values.map (fun x => x.weaken (table.width a)))

private def atom {Γ : List ObjTy} {n : Nat} {a : ObjTy}
    (frame : Frame table Γ n) : Cont.Atom Γ a → Vector (IR.Machine.Atom n) (table.width a)
  | .local x => x.lookup frame
  | .unit => #v[]
  | .bool value => #v[.lit (if value then 1 else 0)]
  | .i32 value => #v[.lit value]

private def arguments {Γ : List ObjTy} {n : Nat} {types : List ObjTy}
    (frame : Frame table Γ n) (values : Args (Cont.Atom Γ) types) :
    Vector (IR.Machine.Atom n) (table.arity types) :=
  table.pack (values.map (atom frame))

private abbrev Joins (table : Table) (layout : List Nat) (joins : List (List ObjTy)) :=
  Args (fun params => Scope.Var Unit layout (table.arity params)) joins

private structure Context where
  source : Lean.Name

private structure State (functions : List IR.Machine.Signature) (layout : List Nat) (result : Nat) where
  next : Nat := 0
  blocks : Std.DHashMap (Fin layout.length)
    (fun i => IR.Machine.Body functions layout result (layout.get i)) := {}

private abbrev Build (table : Table) (source : Oria.Program.ClosedProgram) (layout : List Nat) (result : Nat) :=
  ReaderT Context (StateT (State (IR.Machine.signatures table source) layout result) (Except Diagnostic))

private def reserve {source : Oria.Program.ClosedProgram} {layout : List Nat} {result : Nat}
    (count : Nat) : Build table source layout result (Scope.Var Unit layout count) := do
  let state ← get
  if bound : state.next < layout.length then
    let index : Fin layout.length := ⟨state.next, bound⟩
    if shape : layout.get index = count then
      modify fun state => { state with next := state.next + 1 }
      pure (shape ▸ Scope.Var.ofIndex Unit index)
    else throw (.unsupportedMachineLowering (← read).source)
  else throw (.unsupportedMachineLowering (← read).source)

private def store {layout : List Nat} {n : Nat} {source : Oria.Program.ClosedProgram}
    {result : Nat} (target : Scope.Var Unit layout n)
    (body : IR.Machine.Body (IR.Machine.signatures table source) layout result n) :
    Build table source layout result Unit :=
  modify fun state => { state with
    blocks := state.blocks.insert target.index (target.typeCorrect.symm ▸ body) }

private def define {Γ : List ObjTy} {n : Nat} {source : Oria.Program.ClosedProgram}
    {m : Nat} {layout : List Nat} {result : Nat}
    (frame : Frame table Γ n)
    (operation : IR.Machine.Op (IR.Machine.signatures table source) n m)
    (next : Frame table Γ (m + n) → Vector (IR.Machine.Atom (m + n)) m →
      Build table source layout result (IR.Machine.Body (IR.Machine.signatures table source) layout result (m + n))) :
    Build table source layout result (IR.Machine.Body (IR.Machine.signatures table source) layout result n) := do
  let values := Vector.ofFn fun i : Fin m => IR.Machine.Atom.var (n := m + n) ⟨i.val, by omega⟩
  let frame := frame.map fun values => values.map (fun x => x.weaken m)
  let body ← next frame values
  pure (.step operation body)

private def operation {Γ : List ObjTy} {n : Nat} {g : Grade} {a : ObjTy}
    {source : Oria.Program.ClosedProgram} {layout : List Nat} {result : Nat}
    (frame : Frame table Γ n) (op : Cont.Op Γ g a)
    (yield : ∀ {m}, Option (IR.Machine.Atom m) → Frame table Γ m → Vector (IR.Machine.Atom m) (table.width a) →
      Build table source layout result (IR.Machine.Body (IR.Machine.signatures table source) layout result m)) :
    Build table source layout result (IR.Machine.Body (IR.Machine.signatures table source) layout result n) :=
  match op with
  | .division l r =>
      define frame (.division (atom frame l)[0] (atom frame r)[0]) fun frame values =>
        yield (some values[0]) frame #v[values[1]]
  | .checkpoint forced => define frame (.checkpoint forced) (yield none)
  | .copy value => (yield none) frame (atom frame value)
  | .unary .neg value => define frame (.unary .neg (atom frame value)[0]) (yield none)
  | .unary .not value => define frame (.unary .not (atom frame value)[0]) (yield none)
  | .binary .add l r => define frame (.binary .add (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .binary .sub l r => define frame (.binary .sub (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .binary .mul l r => define frame (.binary .mul (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .binary .le l r => define frame (.binary .le (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .binary .lt l r => define frame (.binary .lt (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .binary .eq l r => define frame (.binary .eq (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .binary .beq l r => define frame (.binary .beq (atom frame l)[0] (atom frame r)[0]) (yield none)
  | .construct (fields := fields) ref args => do
      let ctx ← read
      let layout ← table.layout ref
      if table.product a then
        if same : table.arity fields = table.width a then
          (yield none) frame (same ▸ arguments frame args)
        else throw (.unsupportedRepresentation ctx.source a .body)
      else if one : table.width a = 1 then
        if table.boxed a then
          define frame (.allocate layout (arguments frame args)) fun frame value =>
            (yield none) frame (one.symm ▸ value)
        else (yield none) frame (one.symm ▸ #v[IR.Machine.Atom.lit (n := n) layout.tag])
      else throw (.unsupportedRepresentation ctx.source a .body)
  | .call (sig := sig) ref args => do
      let .named name := ref.key
      let some position := source.members.findFinIdx? (fun member => member.source == name)
        | throw (.unknownFunction name)
      if same : sig = source.members[position].signature then
        let callee := same.symm ▸ IR.Machine.referenceAt table source position
        define frame (.call callee (arguments frame args)) fun frame values =>
          let (flag, values) := unpackResult sig.grade.canFail values
          yield flag frame values
      else throw (.functionSignatureMismatch name source.members[position].signature sig)
  | .command request =>
      request.traverseK (fun {a} value k => do
        if scalar : table.width a = 1 then
          let word : Vector (IR.Machine.Atom n) 1 := scalar ▸ atom frame value
          k word[0]
        else throw (.unsupportedRepresentation (← read).source a .body))
        (fun request => define frame (.command request) fun frame values =>
          let (flag, values) := unpackResult (table := table) (a := .i32) true values
          yield flag frame values)
  | .execute (params := params) (g := g) scope ref args => do
      let .named name := ref.key
      let sig : Signature := ⟨params, .i32, g⟩
      let some position := source.members.findFinIdx? (fun member => member.source == name)
        | throw (.unknownFunction name)
      if same : sig = source.members[position].signature then
        let callee : Scope.Var Unit (IR.Machine.signatures table source)
            (IR.Machine.signature table sig) := same.symm ▸ IR.Machine.referenceAt table source position
        scope.traverseK (fun {a} value k => do
          if scalar : table.width a = 1 then
            let word : Vector (IR.Machine.Atom n) 1 := scalar ▸ atom frame value
            k word[0]
          else throw (.unsupportedRepresentation (← read).source a .body))
          (fun scope => do
            have shape : IR.Machine.signature table sig =
                ⟨table.arity params, g.canFail.toNat + 1⟩ := by
              cases h : g.canFail <;> simp [IR.Machine.signature, sig, h, Table.width, Bool.toNat]
            define frame (.execute scope g.canFail (shape ▸ callee) (arguments frame args)) (yield none))
      else throw (.functionSignatureMismatch name source.members[position].signature sig)
  | .memory operation args => do
      let ctx ← read
      match operation, args with
      | .nbt .forget, .cons value .nil =>
          let value := atom frame value
          (yield none) frame value
      | .nbt op, args =>
          args.traverseK (fun {a} value k => do
            if one : table.width a = 1 then
              let word : Vector (IR.Machine.Atom n) 1 := one ▸ atom frame value
              k word[0]
            else throw (.unsupportedRepresentation ctx.source a .body))
            (fun values => define frame (.nbt op values) fun frame result =>
              if same : op.width = resultWidth table op.grade.canFail a then
                let (flag, values) := unpackResult op.grade.canFail (same ▸ result)
                yield flag frame values
              else throw (.unsupportedMachineLowering ctx.source))
      | .persist (a := a), .cons value .nil =>
          let values := atom frame value
          let existingRef := match a with | .ref _ => true | _ => false
          if existingRef || (table.kinds a).toList.all (fun | .scalar => true | _ => false) then
            (yield none) frame values
          else if one : table.width a = 1 then
            let values : Vector (IR.Machine.Atom n) 1 := one ▸ values
            define frame (.promote a values[0]) fun frame result =>
              (yield none) frame (one.symm ▸ result)
          else throw (.unsupportedRepresentation ctx.source a .body)
      | .rootGet ref, .nil =>
          define frame (.rootGet ⟨ref.name, table.kinds a⟩) (yield none)
      | .rootSet (a := a) ref, .cons value .nil =>
          define frame (.rootSet ⟨ref.name, table.kinds a⟩ (atom frame value)) (yield none)
      | .refNew (a := a), .cons value .nil =>
          define frame (.refNew (table.refLayout a) (atom frame value)) (yield none)
      | .refGet (a := a), .cons cell .nil =>
          define frame (.refGet (table.refLayout a)
            ((atom frame cell).get ⟨0, by simp [Table.width]⟩)) (yield none)
      | .refSet (a := a), .cons cell (.cons value .nil) =>
          define frame (.refSet (table.refLayout a)
            ((atom frame cell).get ⟨0, by simp [Table.width]⟩)
            (atom frame value)) (yield none)

private def project {Γ : List ObjTy} {n : Nat} {a : ObjTy} {fields : List ObjTy}
    {source : Oria.Program.ClosedProgram} {layout : List Nat} {result : Nat}
    (frame : Frame table Γ n) (value : Vector (IR.Machine.Atom n) (table.width a))
    (constructor : Constructor a fields)
    (next : ∀ {m}, Frame table Γ m → Frame table fields m →
      Build table source layout result (IR.Machine.Body (IR.Machine.signatures table source) layout result m)) :
    Build table source layout result (IR.Machine.Body (IR.Machine.signatures table source) layout result n) := do
  match constructor with
  | constructor =>
      let ctx ← read
      let shape ← table.layout constructor
      if table.product a then
        if same : table.width a = table.arity fields then
          next frame (table.unpack fields (same ▸ value))
        else throw (.unsupportedRepresentation ctx.source a .body)
      else if table.boxed a then
        if valid : 0 < table.width a then
          define frame (.project shape value[0]) fun frame payload =>
            next frame (table.unpack fields payload)
        else throw (.unsupportedRepresentation ctx.source a .body)
      else if empty : fields = [] then
        next frame (empty.symm ▸ Args.nil)
      else throw (.unsupportedRepresentation ctx.source a .body)

mutual
  /-- Block declarations contain arities only; source instructions stay in Cont. -/
  private def headers {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
      Cont.Comp Γ result joins → List Nat
    | .fail | .ret _ | .jump _ _ => []
    | .invoke (a := a) _ next failed =>
        (table.arity (a :: Γ) :: headers next) ++ (table.arity Γ :: headers failed)
    | .letOp _ next => headers next
    | .branch _ yes no =>
        (table.arity Γ :: headers yes) ++ (table.arity Γ :: headers no)
    | .switch _ arms => armHeaders arms
    | .letJoin (params := params) body next =>
        (table.arity params :: headers body) ++ headers next

  private def armHeaders {Γ : List ObjTy} {a : ObjTy} {result : ObjTy}
      {joins : List (List ObjTy)} :
      Cont.Arms Γ a result joins → List Nat
    | .nil => []
    | .default body => table.arity Γ :: headers body
    | .cons _ body rest =>
        (table.arity (a :: Γ) :: headers body) ++ armHeaders rest
end

mutual
  private def body {Γ : List ObjTy} {n : Nat} {layout : List Nat} {targets : List (List ObjTy)}
      {result : ObjTy} {source : Oria.Program.ClosedProgram}
      (frame : Frame table Γ n) (joins : Joins table layout targets)
      (comp : Cont.Comp Γ result targets) :
      Build table source layout (resultWidth table escaping result)
        (IR.Machine.Body (IR.Machine.signatures table source) layout (resultWidth table escaping result) n) :=
    match comp with
    | .fail => do
        if escaping then pure (.done (.ret (returned escaping false (Vector.replicate (table.width result) (.lit 0)))))
        else throw (.unsupportedMachineLowering (← read).source)
    | .ret value => pure (.done (.ret (returned escaping true (atom frame value))))
    | .jump target values =>
        pure (.done (.jump ⟨target.lookup joins, arguments frame values⟩))
    | .letOp op next => operation frame op fun flag frame value => do
        if flag.isSome then throw (.unsupportedMachineLowering (← read).source)
        body (.cons value frame) joins next
    | .invoke op next failed => operation frame op fun flag frame value => do
        let yes ← block joins next
        let no ← block joins failed
        let yes := IR.Machine.Edge.mk yes (table.pack (.cons value frame))
        let no := IR.Machine.Edge.mk no (table.pack frame)
        match flag with
        | none => pure (.done (.jump yes))
        | some flag => pure (.done (.branch (.isTrue flag) yes no))
    | .branch condition yes no => do
        let yes ← block joins yes
        let no ← block joins no
        pure (.done (.branch (.isTrue (atom frame condition)[0]) ⟨yes, table.pack frame⟩ ⟨no, table.pack frame⟩))
    | .switch (a := a) value arms => do
        let words := atom frame value
        if table.product a || table.singleConstructor a then
          let (cases, fallback) ← lowerArms frame joins words arms
          match cases, fallback with
          | [(_, edge)], _ | [], some edge => pure (.done (.jump edge))
          | _, _ => throw (.unsupportedMachineLowering (← read).source)
        else if scalar : 0 < table.width a then
          if table.boxed a then
            define frame (.tag words[0]) fun frame tag => do
              let (cases, fallback) ← lowerArms frame joins (words.map (·.weaken 1)) arms
              pure (.done (.switch tag[0] cases fallback))
          else
            let (cases, fallback) ← lowerArms frame joins words arms
            pure (.done (.switch words[0] cases fallback))
        else throw (.unsupportedRepresentation (← read).source a .body)
    | .letJoin (params := params) nested next => do
        let target ← block joins nested
        body frame (.cons target joins) next
  termination_by (sizeOf comp, 0)
  decreasing_by all_goals simp_wf <;> omega

  private def block {layout : List Nat} {targets : List (List ObjTy)} {Γ : List ObjTy}
      {result : ObjTy} {source : Oria.Program.ClosedProgram}
      (joins : Joins table layout targets) (comp : Cont.Comp Γ result targets) :
      Build table source layout (resultWidth table escaping result) (Scope.Var Unit layout (table.arity Γ)) := do
    let target ← reserve (table.arity Γ)
    let ctx ← read
    for a in Γ do table.check ctx.source .body a
    let value ← body (parameters Γ) joins comp
    store target value
    pure target
  termination_by (sizeOf comp, 1)
  decreasing_by exact Prod.Lex.right _ (by decide)

  private def lowerArms {Γ : List ObjTy} {n : Nat} {layout : List Nat}
      {targets : List (List ObjTy)} {a : ObjTy} {result : ObjTy}
      {source : Oria.Program.ClosedProgram}
      (frame : Frame table Γ n) (joins : Joins table layout targets)
      (value : Vector (IR.Machine.Atom n) (table.width a)) (arms : Cont.Arms Γ a result targets) :
      Build table source layout (resultWidth table escaping result)
        (List (Int32 × IR.Machine.Edge layout n) × Option (IR.Machine.Edge layout n)) :=
    match arms with
    | .nil => pure ([], none)
    | .default comp => do
        let target ← block joins comp
        pure ([], some ⟨target, table.pack frame⟩)
    | .cons constructor comp rest => do
        let target ← armBlock joins constructor comp
        let tag ← table.tag constructor
        let (cases, fallback) ← lowerArms frame joins value rest
        pure ((tag, ⟨target, table.pack (.cons value frame)⟩) :: cases, fallback)
  termination_by (sizeOf arms, 0)
  decreasing_by all_goals simp_wf <;> omega

  private def armBlock {layout : List Nat} {targets : List (List ObjTy)} {a : ObjTy}
      {fields Γ : List ObjTy} {result : ObjTy} {source : Oria.Program.ClosedProgram}
      (joins : Joins table layout targets) (constructor : Constructor a fields)
      (comp : Cont.Comp (fields ++ Γ) result targets) :
      Build table source layout (resultWidth table escaping result) (Scope.Var Unit layout (table.arity (a :: Γ))) := do
    let target ← reserve (table.arity (a :: Γ))
    let frame := parameters (a :: Γ)
    let .cons value frame := frame
    let code ← project frame value constructor fun frame payload =>
      body (payload.append frame) joins comp
    store target code
    pure target
  termination_by (sizeOf comp, 1)
  decreasing_by exact Prod.Lex.right _ (by decide)

end

private def lowerMember (table : Table) (source : Oria.Program.ClosedProgram)
    (position : Fin source.members.size) :
    Except Diagnostic (IR.Machine.Def (IR.Machine.signatures table source)
      (IR.Machine.signature table source.members[position].signature)) := do
  let member := source.members[position]
  table.check member.source .result member.signature.result
  for (a, index) in member.signature.args.zipIdx do
    table.check member.source (.parameter index) a
  let comp := member.body.computation
  let layout := table.arity member.signature.args :: headers (table := table) comp
  let ((entry, state)) ←
    (block (escaping := member.signature.grade.canFail) (source := source) (layout := layout) .nil comp).run ⟨member.source⟩ |>.run {}
  let blocks ← Data.IndexedVector.ofFnM fun i : Fin layout.length =>
    match state.blocks.get? i with
    | some body => pure body
    | none => throw (.unsupportedMachineLowering member.source)
  Optimize.Machine.run member.source (IR.Machine.referenceAt table source position) ⟨layout, entry, blocks⟩

/-- Physical metadata prepared before runtime-library generation. -/
public structure Prepared where
  table : Table
  persistent : Representation.Persistent.PlanTable

public def prepare (candidate : Oria.Program.CollectionCandidate) : Except Diagnostic Prepared := do
  let table ← Table.build candidate.schemas
  let persistentTypes := candidate.members.foldl (init := ({} : Std.HashSet ObjTy))
    fun types member => types ∪ member.dependencies.persistentTypes
  let persistent ← Representation.Persistent.build table persistentTypes.toArray
  pure ⟨table, persistent⟩

/-- Lower members using the same metadata that configured the runtime library. -/
public def lowerProgram (source : Oria.Program.ClosedProgram) (prepared : Prepared) :
    Except Diagnostic (IR.Machine.Program source) := do
  let table := prepared.table
  let definitions ← Data.IndexedVector.ofFnM fun i : Fin (IR.Machine.signatures table source).length => do
    let position := IR.Machine.memberPosition table source i
    let definition ← lowerMember table source position
    have shape : IR.Machine.signature table source.members[position].signature =
        (IR.Machine.signatures table source).get i := by
      simp [IR.Machine.signatures, IR.Machine.memberPosition, position]
    pure (shape ▸ definition)
  let program ← Optimize.Constants.run ⟨table, definitions, prepared.persistent⟩
  let program ← Optimize.Conditions.run program
  Optimize.DeadCode.run program

end Oria.Lower.Machine
