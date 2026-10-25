module

public meta import Lean.Elab.BuiltinTerm
public meta import Lean.ScopedEnvExtension

public meta section

namespace Oria.StringLiteral

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

private initialize constructors : SimpleScopedEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := Array.push
    exportEntry? := fun env entry =>
      let visible := env.contains entry.1 && env.contains entry.2
      let exported := if visible then some entry else none
      { exported, server := exported, «private» := some entry }
  }

private def checkConstructor (target constructor : Name) : MetaM Unit := do
  unless (← getConstInfo target).levelParams.isEmpty do
    throwError "string_literal targets must be monomorphic"
  let type ← mkConstWithFreshMVarLevels target
  unless ← isDefEq (← inferType type) (mkSort Level.one) do
    throwError "string_literal targets must be closed types"
  let ctor ← mkConstWithFreshMVarLevels constructor
  forallTelescope (← inferType ctor) fun args result => do
    let some first := args[0]? | throwError "string_literal constructors must accept a String"
    unless (← first.fvarId!.getDecl).binderInfo.isExplicit &&
        (← isDefEq (← inferType first) (mkConst ``String)) do
      throwError "string_literal constructors must accept an explicit String first"
    for arg in args[1:] do
      let domain ← inferType arg
      unless domain.isAutoParam && (← isProp domain) do
        throwError "string_literal constructors may only require automatic proofs after the String"
    unless ← isDefEq result type do
      throwError "string_literal constructor must return {type}"

/-- Register a type's existing checked constructor for string literal elaboration. -/
initialize registerBuiltinAttribute {
  name := `string_literal
  descr := "checked string literal constructor for a domain type"
  add := fun target stx kind => do
    let ctorStx ← Attribute.Builtin.getIdent stx
    let constructor ← realizeGlobalConstNoOverloadWithInfo ctorStx
    (checkConstructor target constructor).run' {}
    constructors.add (target, constructor) kind
}

/-- Expected types select domain constructors; ordinary strings use Lean's builtin elaborator. -/
@[term_elab str]
def elaborate : TermElab := fun stx expectedType? => do
  let some expected := expectedType? | throwUnsupportedSyntax
  let expected ← instantiateMVars expected
  if expected.hasExprMVar then throwUnsupportedSyntax
  if expected.isConstOf ``String then throwUnsupportedSyntax
  let candidates ← (constructors.getState (← getEnv)).filterM fun (target, _) =>
    withNewMCtxDepth <| isDefEq expected (mkConst target)
  let (target, constructor) ← match candidates.toList with
    | [] => throwUnsupportedSyntax
    | [entry] => pure entry
    | _ => throwErrorAt stx "ambiguous string literal for {expected}; use an explicit constructor"
  let literal : TSyntax `term := ⟨stx⟩
  let application ← `($(mkIdent constructor) $literal)
  try
    withoutErrToSorry <| withSynthesize <| elabTermEnsuringType application expected
  catch
    | .error _ _ => throwErrorAt stx "invalid string literal for {target}: {stx}"
    | ex => throw ex

end Oria.StringLiteral
