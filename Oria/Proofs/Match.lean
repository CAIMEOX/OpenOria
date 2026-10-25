module

import Oria
public import Oria.Language.Object
import Oria.Proofs.Fixtures.MaybeI32
import Oria.IR.Tree.Pretty
import Oria.IR.Cont.Pretty
import Oria.Compiler.Definition
import Oria.IR.Cont.Semantics
import Oria.Proofs.Fixtures.Envelope
meta import Oria
meta import Oria.Proofs.Fixtures.MaybeI32
meta import Oria.IR.Tree.Pretty
meta import Oria.IR.Cont.Pretty
meta import Oria.Compiler.Definition
meta import Oria.IR.Cont.Semantics
meta import Oria.Proofs.Fixtures.Envelope

namespace Oria.Proofs.Match

open Oria Oria.Proofs.Fixtures Lean Lean.Elab.Command

public inductive PairPayload where
  | pair (left right : Int32)
  deriving Oria.Object

private def model : Semantics.Cont.Model Unit := {
  unary := fun
    | .neg, .i32 n => pure (.returned (.i32 (-n)))
    | .not, .bool b => pure (.returned (.bool (!b)))
  binary := fun
    | .add, .i32 x, .i32 y => pure (.returned (.i32 (x + y)))
    | .sub, .i32 x, .i32 y => pure (.returned (.i32 (x - y)))
    | .mul, .i32 x, .i32 y => pure (.returned (.i32 (x * y)))
    | .le, .i32 x, .i32 y => pure (.returned (.bool (x ≤ y)))
    | .lt, .i32 x, .i32 y => pure (.returned (.bool (x < y)))
    | .eq, .i32 x, .i32 y => pure (.returned (.bool (x == y)))
    | .beq, .bool x, .bool y => pure (.returned (.bool (x == y)))
  construct := fun _ _ => pure .failed
  call := fun _ _ => pure .failed
  command := fun _ => pure .failed
  execute := fun _ _ _ => pure .failed
  memory := fun _ _ => pure .failed
  project := fun {_owner fields} constructor value =>
    pure <| if constructor.name == ``PairPayload.pair then
        if h : fields = [.i32, .i32] then
          some (h.symm ▸ Args.cons (.i32 29) (.cons (.i32 11) .nil))
        else none
      else if constructor.name == ``Envelope.wrap then
        if h : fields = [.data MaybeI32.Oria.id] then
          some (h.symm ▸ Args.cons (.data ⟨value.token⟩) .nil)
        else none
      else if constructor.name == ``MaybeI32.some then
        if h : fields = [.i32] then
          if value.token == 0 then none
          else some (h.symm ▸ Args.cons (.i32 (Int32.ofNat (value.token - 1))) .nil)
        else none
      else if h : fields = [] then
        let tag := if constructor.name == ``MaybeI32.none || constructor.name == ``Choice.rock then 0
          else if constructor.name == ``Choice.paper then 1 else 2
        if tag == value.token then some (h.symm ▸ Args.nil) else none
      else none
}

private def compile (source : Name) : CommandElabM ElaboratedDef := do
  let .ok definition := McFunctionRegistry.elaborate (← getEnv) source
    | throwError "fixture did not elaborate: {source}"
  pure definition

private def lower (definition : ElaboratedDef) : CommandElabM (IR.Cont.Def definition.signature) := do
  let .ok objects := ObjectCatalog.build [Choice.Oria.schema, PairPayload.Oria.schema,
      MaybeI32.Oria.schema, Envelope.Oria.schema]
    | throwError "object catalog did not build"
  let .ok commands := Command.Catalog.build []
    | throwError "command catalog did not build"
  let .ok functions := Function.Catalog.build [definition]
    | throwError "function catalog did not build"
  match Compiler.compile functions objects commands definition with
  | .ok cont => pure cont
  | .error diagnostic => throwError "pattern matrix did not lower: {repr diagnostic}"

@[mcfunction]
private def priority (x y : Val Choice) : Prog .pure Int32 := do
  match x, y with
  | .rock, _ => return 10
  | _, .rock => return 20
  | _, _ => return 30

run_cmd
  let definition ← compile ``priority
  let text := definition.definition.pretty 100
  unless (text.splitOn "return ").length == 4 do
    throwError "Tree must retain each of the three source match bodies exactly once"
  unless (text.splitOn "match ").length == 2 do
    throwError "Tree must retain the source pattern matrix"
  let cont ← lower definition
  let text := cont.pretty 100
  unless (text.splitOn "switch ").length == 3 do
    throwError "match must test each subject only once along a path:\n{text}"
  unless (text.splitOn "return ").length == 4 do
    throwError "source match bodies must remain shared joins:\n{text}"
  let expected : Signature := ⟨[.data Choice.Oria.id, .data Choice.Oria.id], .i32, .pure⟩
  if same : definition.signature = expected then
    let body := (same ▸ cont).computation
    for x in [:3] do
      for y in [:3] do
        let env := Args.cons (Semantics.Cont.Value.data ⟨x⟩) (.cons (.data ⟨y⟩) .nil)
        let expected : Int32 := if x == 0 then 10 else if y == 0 then 20 else 30
        match Id.run ((Semantics.Cont.eval model 100 env .nil body).run ()) with
        | (some (.returned (.i32 actual)), _) =>
            unless actual == expected do throwError "source row priority changed at {x}, {y}"
        | _ => throwError "priority fixture did not return at {x}, {y}"
  else throwError "priority fixture signature changed"

@[mcfunction]
private def nested (value : Val (Option (Option Int32))) : Prog .pure Int32 := do
  match value with
  | .some (.some x) => return x
  | .some .none => return 10
  | .none => return 20

@[mcfunction]
private def payloads (left right : Val (Option Int32)) : Prog .pure Int32 := do
  match left, right with
  | .some x, .some y => return x - y
  | _, _ => return -1

@[mcfunction]
private def continued (value : Val (Option Int32)) (extra : Val Int32) : Prog .pure Int32 :=
  Prog.bind (Oria.Option.elim value (Prog.pure (0 : Val Int32)) Prog.pure) fun selected =>
    Prog.pure (selected + extra)

@[mcfunction]
private def retain (value : Val (Option Int32)) : Prog .pure Int32 := do
  match value with
  | whole =>
      match whole with
      | .some x => return x
      | .none => return 0

@[mcfunction]
private def optionMatch (value : Val (Option Int32)) (fallback : Val Int32) :
    Prog .pure Int32 := do
  match value with
  | .none => return fallback
  | .some x => return x

@[mcfunction]
private def pair (value : Val PairPayload) : Prog .pure Int32 := do
  match value with
  | .pair x y => return x - y

@[mcfunction]
private def envelope (value : Val Envelope) : Prog .pure Int32 := do
  match value with
  | .wrap (.some x) => return x
  | .wrap .none => return 0

@[mcfunction]
private def missing (value : Val Choice) : Prog .pure Int32 := do
  match value with
  | .rock => return 0

@[mcfunction]
private def redundant (value : Val Choice) : Prog .pure Int32 := do
  match value with
  | _ => return 0
  | .rock => return 1

run_cmd
  let definition ← compile ``nested
  let cont ← lower definition
  let expected : Signature := ⟨[.option (.option .i32)], .i32, .pure⟩
  let .isTrue same := decEq definition.signature expected
    | throwError "nested fixture signature changed"
  let body := (same ▸ cont).computation
  for (value, expected) in [
      (Semantics.Cont.Value.some (.some (.i32 42)), 42),
      (.some .none, 10), (.none, 20)] do
    match Id.run ((Semantics.Cont.eval model 100 (.cons value .nil) .nil body).run ()) with
    | (some (.returned (.i32 actual)), _) =>
        unless actual == expected do throwError "nested pattern bound the wrong payload"
    | _ => throwError "nested pattern did not return"

run_cmd
  let definition ← compile ``payloads
  let cont ← lower definition
  let expected : Signature := ⟨[.option .i32, .option .i32], .i32, .pure⟩
  if same : definition.signature = expected then
    let body := (same ▸ cont).computation
    let env := Args.cons (Semantics.Cont.Value.some (.i32 29))
      (.cons (.some (.i32 11)) .nil)
    match Id.run ((Semantics.Cont.eval model 100 env .nil body).run ()) with
    | (some (.returned (.i32 18)), _) => pure ()
    | _ => throwError "multi-column pattern changed binder order"
  else throwError "payload fixture signature changed"

run_cmd
  let definition ← compile ``continued
  let cont ← lower definition
  let expected : Signature := ⟨[.option .i32, .i32], .i32, .pure⟩
  if same : definition.signature = expected then
    let body := (same ▸ cont).computation
    for (value, expected) in [(Semantics.Cont.Value.some (.i32 29), 40), (.none, 11)] do
      let env := Args.cons value (.cons (.i32 11) .nil)
      match Id.run ((Semantics.Cont.eval model 100 env .nil body).run ()) with
      | (some (.returned (.i32 actual)), _) =>
          unless actual == expected do throwError "non-tail match lost its continuation environment"
      | _ => throwError "non-tail match did not return"
    unless (cont.pretty 100 |>.splitOn " <- add ").length == 2 do
      throwError "non-tail match duplicated its continuation"
  else throwError "continuation fixture signature changed"

run_cmd
  let definition ← compile ``retain
  let cont ← lower definition
  let expected : Signature := ⟨[.option .i32], .i32, .pure⟩
  if same : definition.signature = expected then
    let body := (same ▸ cont).computation
    match Id.run ((Semantics.Cont.eval model 100 (.cons (.some (.i32 19)) .nil) .nil body).run ()) with
    | (some (.returned (.i32 19)), _) => pure ()
    | _ => throwError "wildcard binder lost its whole subject"
  else throwError "retained subject fixture signature changed"

run_cmd
  let definition ← compile ``optionMatch
  let cont ← lower definition
  let expected : Signature := ⟨[.option .i32, .i32], .i32, .pure⟩
  if same : definition.signature = expected then
    let body := (same ▸ cont).computation
    for (value, expected) in [(Semantics.Cont.Value.some (.i32 29), 29), (.none, 11)] do
      let env := Args.cons value (.cons (.i32 11) .nil)
      match Id.run ((Semantics.Cont.eval model 100 env .nil body).run ()) with
      | (some (.returned (.i32 actual)), _) =>
          unless actual == expected do throwError "option match returned the wrong value"
      | _ => throwError "option match did not return normally"
  else throwError "option fixture signature changed"

run_cmd
  for (source, owner, value, expected) in [(``pair, PairPayload.Oria.id, 0, (18 : Int32)),
      (``envelope, Envelope.Oria.id, 38, 37), (``envelope, Envelope.Oria.id, 0, 0)] do
    let definition ← compile source
    let cont ← lower definition
    let signature : Signature := ⟨[.data owner], .i32, .pure⟩
    if same : definition.signature = signature then
      let body := (same ▸ cont).computation
      match Id.run ((Semantics.Cont.eval model 100 (.cons (.data ⟨value⟩) .nil) .nil body).run ()) with
      | (some (.returned (.i32 actual)), _) =>
          unless actual == expected do throwError "ADT payload order changed in {source}"
      | _ => throwError "ADT pattern did not return in {source}"
    else throwError "ADT fixture signature changed"

run_cmd
  let .ok objects := ObjectCatalog.build [Choice.Oria.schema]
    | throwError "object catalog did not build"
  let .ok commands := Command.Catalog.build []
    | throwError "command catalog did not build"
  for (source, expected) in [(``missing, Diagnostic.nonExhaustiveMatch ``missing),
      (``redundant, Diagnostic.redundantPattern ``redundant 1)] do
    let definition ← compile source
    let .ok functions := Function.Catalog.build [definition]
      | throwError "function catalog did not build"
    match Compiler.compile functions objects commands definition with
    | .error diagnostic =>
        unless diagnostic == expected do throwError "unexpected match diagnostic: {repr diagnostic}"
    | .ok _ => throwError "invalid pattern matrix was accepted"

/-- A shared join observes exactly the argument telescope supplied by its caller. -/
theorem join_arguments {Γ params : List ObjTy} {result : ObjTy}
    {targets : List (List ObjTy)}
    (model : Semantics.Cont.Model Unit)
    (env : Semantics.Cont.Env Γ) (joins : Semantics.Cont.JoinEnv result targets Unit)
    (body : IR.Cont.Comp params result targets) (values : Args (IR.Cont.Atom Γ) params)
    (fuel : Nat) :
    Semantics.Cont.eval model (fuel + 2) env joins
        (.letJoin body (.jump IR.Scope.Var.head values)) =
      Semantics.Cont.eval model fuel (Semantics.Cont.evalArgs env values) joins body := by
  rw [Semantics.Cont.eval_letJoin, Semantics.Cont.eval_jump, IR.Scope.Var.lookup_head]

end Oria.Proofs.Match
