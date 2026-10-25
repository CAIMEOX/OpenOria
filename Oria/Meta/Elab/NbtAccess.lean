module

public meta import Oria.Language.TypedNbt
public meta import Oria.Meta.Elab.Program.Internal
meta import all Oria.Meta.Elab.Program.Internal
public meta import Lean.Elab.Term
public meta import Qq.MetaM

public meta section

namespace Oria.Elab.NbtAccess

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Qq

private structure Selection where
  root : Expr
  path : Expr
  element : Expr

private def integer (stx : Syntax) : TermElabM Expr := do
  let value ← Term.withSynthesize <| Term.elabTerm stx none
  let type ← whnf (← inferType value)
  if (← Program.Internal.carrier? type).isSome then
    ensureHasType q(Val Int32) value
  else if type.isConstOf ``Nat then mkAppM ``Int32.ofNat #[value]
  else if type.isConstOf ``Int then mkAppM ``Int32.ofInt #[value]
  else ensureHasType q(Int32) value

private def root? (stx : Syntax) : TermElabM (Option Selection) := do
  let saved ← saveState
  try
    let value ← Term.withoutErrToSorry <| Term.elabTerm stx none
    let type ← whnf (← inferType value)
    let (a, repr) ← match_expr type with
      | Oria.Nbt.Global a repr => pure (a, repr)
      | Oria.Nbt.Location a repr => pure (a, repr)
      | _ => do
          let some carrier ← Program.Internal.carrier? type | saved.restore; return none
          let_expr Oria.Nbt.Ref a repr := (← whnf carrier.source) | saved.restore; return none
          pure (a, repr)
    let path ← mkAppOptM ``Oria.Nbt.Access.root #[some q(Val Int32), some a, some repr]
    return some ⟨value, path, a⟩
  catch
    | .error .. => saved.restore; return none
    | ex => throw ex

private def field (selection : Selection) (name : Ident) : TermElabM Selection := do
  let source ← whnf selection.element
  let .const owner _ := source.getAppFn
    | throwErrorAt name "a typed NBT field requires a derived record"
  addCompletionInfo <| CompletionInfo.fieldId name name.getId (← getLCtx) owner
  let env ← getEnv
  let info := do
    let parent ← findField? env owner name.getId
    getFieldInfo? env parent name.getId
  let some info := info
    | throwErrorAt name "unknown NBT field `{name}` of {source}"
  let owner := (privateToUserName? owner).getD owner
  let accessor := mkIdentFrom name (`_root_ ++ owner ++ `Nbt ++ name.getId)
  let fn ← Term.elabTerm accessor none
  let (args, binders, type) ← forallMetaTelescopeReducing (← inferType fn)
  let_expr Oria.Nbt.Access index origin target _ _ := type
    | throwErrorAt name "use `deriving Nbt.Repr` to obtain typed field paths"
  unless (← isDefEq index q(Val Int32)) && (← isDefEq origin source) do
    throwErrorAt name "the derived NBT field does not select from {source}"
  for i in [:args.size] do
    if binders[i]!.isInstImplicit && args[i]!.isMVar then
      args[i]!.mvarId!.assign (← synthInstance (← inferType args[i]!))
  let path ← mkAppM ``Oria.Nbt.Access.then #[selection.path, ← instantiateMVars (mkAppN fn args)]
  addConstInfo name info.projFn
  return { selection with path, element := ← instantiateMVars target }

/- Selection follows Lean's parsed field/index syntax. Its resulting Access is checked
against the derived source/target types by the existing path constructors. -/
private partial def selection? (stx : Syntax) : TermElabM (Option Selection) := do
  if let some root ← root? stx then return some root
  match stx with
  | `(($value)) => selection? value
  | `($value:term[$index:term]) =>
      let some selection ← selection? value | return none
      let_expr Array element := (← whnf selection.element)
        | throwErrorAt index "typed NBT indexing requires an Array field"
      let index ← integer index
      let index ← if (← Program.Internal.carrier? (← inferType index)).isSome then pure index
        else mkAppM ``Oria.I32.lit #[index]
      let path ← mkAppM ``Oria.Nbt.Access.at #[selection.path, index]
      return some { selection with path, element }
  | `($value:term.$name:ident) =>
      let some selection ← selection? value | return none
      return some (← field selection name)
  | _ =>
      if stx.isIdent then
        let .str base name := stx.getId | return none
        if base.isAnonymous then return none
        let some selection ← selection? (mkIdentFrom stx base) | return none
        let ref := stx.identComponents.getLast!
        return some (← field selection ⟨mkIdentFrom ref (.mkSimple name)⟩)
      return none

private def candidate (stx : Syntax) : Bool :=
  stx.isIdent || stx.isOfKind ``Lean.Parser.Term.proj ||
    stx.isOfKind ``Lean.Parser.Term.paren || (match stx with | `($_:term[$_:term]) => true | _ => false)

/-- An arrow-bound I32 selection performs one native read and retains Failure. -/
def read? (stx : Syntax) : TermElabM (Option Expr) := do
  unless candidate stx do return none
  let some selection ← selection? stx | return none
  unless ← isDefEq selection.element q(Int32) do
    throwErrorAt stx "NBT selection binds I32 values; use `Nbt.snapshot` to copy {selection.element}"
  return some (← mkAppM ``Oria.Nbt.readI32 #[selection.root, selection.path])

/-- Assignment selects a host literal or an object I32 source, then uses typed NBT set. -/
def write? (lhs rhs : Syntax) : TermElabM (Option Expr) := do
  let some selection ← selection? lhs | return none
  let value ← if ← isDefEq selection.element q(Int32) then do
      let value ← integer rhs
      if (← Program.Internal.carrier? (← inferType value)).isSome then
        mkAppM ``Oria.Nbt.Source.i32 #[value]
      else
        mkAppM ``Oria.Nbt.Source.literal #[value]
    else do
      let value ← Term.elabTermEnsuringType rhs selection.element
      mkAppM ``Oria.Nbt.Source.literal #[value]
  return some (← mkAppM ``Oria.Nbt.set #[selection.root, selection.path, value])

end Oria.Elab.NbtAccess
