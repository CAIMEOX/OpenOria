module

public meta import Oria.Meta.Elab.Program.Internal
public meta import Oria.Meta.ObjectDerive
public meta import Lean.Elab.App
public meta import Lean.Elab.StructInst
meta import all Lean.Elab.StructInst
meta import all Oria.Meta.Elab.Program.Internal
public meta import Qq.MetaM

public meta section

namespace Oria.Elab.Record

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Qq

private abbrev Carrier := Program.Internal.Carrier

/- Lean's structure metadata and constructor elaboration provide field names and typing.
The stage adapter substitutes object carriers for the constructor's host fields; native
structure projection instead expects the host structure itself, rather than `Val A`.
-/
private structure View where
  carrier : Carrier
  info : StructureInfo
  fields : Array Carrier
  builder : Expr
  arguments : Array Expr
  positions : Array Nat

private def view? (carrier : Carrier) : TermElabM (Option View) := do
  let source ← whnf carrier.source
  let .const owner _ := source.getAppFn | return none
  let some info := getStructureInfo? (← getEnv) owner | return none
  let constructor := getStructureCtor (← getEnv) owner
  let some name := ObjectRegistry.builder? (← getEnv) constructor.name | return none
  let builder ← mkConstWithFreshMVarLevels name
  let (arguments, binders, result) ← forallMetaTelescopeReducing (← inferType builder)
  let expected := { carrier with region := q(Region.any) }
  unless ← isDefEq result (expected.toComputationType q(Grade.pure)) do
    throwError "the record constructor does not produce the expected object type"
  for i in [:arguments.size] do
    if binders[i]!.isInstImplicit then
      arguments[i]!.mvarId!.assign (← synthInstance (← inferType arguments[i]!))
  let mut fields := #[]
  let mut positions := #[]
  for i in [:arguments.size] do
    if let some field ← Program.Internal.carrier? (← inferType arguments[i]!) then
      fields := fields.push field
      positions := positions.push i
  return some { carrier, info, fields, builder, arguments, positions }

private def project (view : View) (index : Nat) (value : Expr) : TermElabM Expr := do
  let some fieldName := view.info.fieldNames[index]? | throwError "unknown object record field"
  let some info := getFieldInfo? (← getEnv) view.info.structName fieldName | throwUnsupportedSyntax
  let some name := ObjectRegistry.projection? (← getEnv) info.projFn | throwUnsupportedSyntax
  mkAppM name #[value]

/- Lean's host expansion flattens parent structures. Object constructors retain
parent objects, so this adapter groups Lean's parsed paths by direct fields. -/
private def groupFields (view : View) (fields : Array StructInst.FieldView) :
    TermElabM (Std.HashMap Name (Array StructInst.FieldView)) := do
  fields.foldlM (init := {}) fun groups field => do
    let (ref, name, rest) ← match field.lhs with
      | .fieldName id :: rest => pure (id, id.getId, rest)
      | .fieldIndex ref i :: rest =>
          let some name := view.info.fieldNames[i - 1]?
            | throwErrorAt ref "object record field index is out of bounds"
          if i == 0 then throwErrorAt ref "object record field indices start at 1"
          pure (ref, name, rest)
      | _ => throwErrorAt field.ref "object record updates use named fields"
    addCompletionInfo <| CompletionInfo.fieldId ref name (← getLCtx) view.info.structName
    let some info := getFieldInfo? (← getEnv) view.info.structName name
      | throwErrorAt ref "unknown field `{name}` of {view.carrier.source}"
    addConstInfo ref info.projFn
    let previous := groups.getD name #[]
    if (!previous.isEmpty && rest.isEmpty) || previous.any (·.lhs.isEmpty) then
      throwErrorAt ref "field `{name}` has already been specified"
    return groups.insert name (previous.push {field with lhs := rest})

private partial def construct (view : View) (fields : Array StructInst.FieldView)
    (source? : Option Expr) : TermElabM Expr := do
  let provided ← groupFields view fields
  let rec fill (pending : List (Fin view.fields.size)) (args : Array Expr)
      (source? : Option Expr) : TermElabM Expr := do
    match pending with
    | [] => return mkAppN view.builder args
    | i :: rest =>
      let field := view.fields[i]
      let name := view.info.fieldNames[i.val]!
      let position := view.positions[i.val]!
      match provided[name]? with
      | some children =>
          let some first := children[0]? | throwError "empty object update path"
          if first.lhs.isEmpty then
            let value ← Term.elabTermEnsuringType first.val field.toType
            fill rest (args.set! position value) source?
          else
            let some child ← view? field
              | throwErrorAt first.ref "nested object updates require a derived record field"
            let previous ← source?.mapM (project view i.val)
            let action ← construct child children previous
            withLocalDeclD name field.toType fun value => do
              let body ← fill rest (args.set! position value) source?
              mkAppM ``Prog.bind #[action, ← mkLambdaFVars #[value] body]
      | none =>
          let some source := source?
            | throwError "missing object record field `{name}`"
          let value ← ensureHasType field.toType (← project view i.val source)
          fill rest (args.set! position value) source?
  match source? with
  | none => fill (List.finRange view.fields.size) view.arguments none
  | some value =>
      let value ← ensureHasType view.carrier.toType value
      withLocalDeclD `record view.carrier.toType fun source => do
        let body ← fill (List.finRange view.fields.size) view.arguments (some source)
        let initial ← mkAppM ``Prog.pure #[value]
        mkAppM ``Prog.bind #[initial, ← mkLambdaFVars #[source] body]

/-- Construct or update an object record, checking each field against its derived carrier.
An update binds its source once and constructs a fresh arena-neutral value. -/
def elaborate? (stx : Syntax) (expected? : Option Expr) : TermElabM (Option Expr) := do
  unless stx.isOfKind ``Lean.Parser.Term.structInst do return none
  let `(Lean.Parser.Term.structInst| { $[$sources,* with]? $_:structInstField,* }) := stx
    | return none
  let sources := (sources.map (·.getElems)).getD #[]
  let value? ← sources[0]?.mapM fun source => Term.elabTerm source.raw none
  let carrier? ← match value? with
    | some value => Program.Internal.carrier? (← inferType value)
    | none => match expected? with
      | some type => (Program.Internal.computation? type) <&> fun type => type.map (·.toCarrier)
      | none => pure none
  let some carrier := carrier? | return none
  let some view ← view? carrier | return none
  if sources.size > 1 then throwErrorAt stx "an object record update takes one source"
  let parsed ← liftMacroM <| StructInst.mkStructView stx ⟨#[], none, false⟩
  let result ← construct view parsed.fields value?
  match expected? with
  | some type => return some (← ensureHasType type result)
  | none => return some result

/-- Expected object computations select record construction; host structures use Lean. -/
@[term_elab Lean.Parser.Term.structInst]
def elaborate : TermElab := fun stx expected? => do
  let some result ← elaborate? stx expected? | throwUnsupportedSyntax
  return result

/-- Resolve source-record fields using Lean's structure metadata and the derived constructor. -/
@[term_elab ident, term_elab Lean.Parser.Term.proj]
def elaborateProjection : TermElab := fun stx expected? => do
  let (receiver, field) ← match stx with
    | `($receiver:term.$field:ident) => pure (receiver, field)
    | _ =>
      unless stx.isIdent do throwUnsupportedSyntax
      let .str base field := stx.getId | throwUnsupportedSyntax
      if base.isAnonymous then throwUnsupportedSyntax
      pure (⟨mkIdentFrom stx base⟩, mkIdentFrom stx (.mkSimple field))
  let saved ← saveState
  let value ← try Term.elabTerm receiver none catch _ =>
    saved.restore
    throwUnsupportedSyntax
  let some carrier ← Program.Internal.carrier? (← inferType value) | throwUnsupportedSyntax
  let .const owner _ := (← whnf carrier.source).getAppFn | throwUnsupportedSyntax
  let some info := getFieldInfo? (← getEnv) owner field.getId | throwUnsupportedSyntax
  let some name := ObjectRegistry.projection? (← getEnv) info.projFn | throwUnsupportedSyntax
  let result ← mkAppM name #[value]
  addConstInfo field info.projFn
  match expected? with
  | some type => ensureHasType type result
  | none => pure result

end Oria.Elab.Record
