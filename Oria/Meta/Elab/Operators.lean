module

public meta import Oria.Language.Builder
public meta import Lean.Elab.Extra
public meta import Oria.Meta.Elab.Program.Internal
meta import all Oria.Meta.Elab.Program.Internal
public meta import Qq.MetaM

public meta section

namespace Oria.Elab.Operators

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Qq

private def objectCode? (type : Expr) : MetaM (Option Expr) := do
  return (← Program.Internal.carrier? type).map (·.code)

private def operand (a : ObjTy) (value : Expr) : TermElabM Expr := do
  let type ← instantiateMVars (← inferType value)
  let target := if a == .bool then q(Val Bool) else q(Val Int32)
  if (← objectCode? type).isSome || type.hasExprMVar then
    return ← ensureHasType target value
  match a with
  | .bool => mkAppM ``Oria.Bool.lit #[← ensureHasType q(Bool) value]
  | .i32 =>
      let value ← if type.isConstOf ``Nat then mkAppM ``Int32.ofNat #[value]
        else if type.isConstOf ``Int then mkAppM ``Int32.ofInt #[value]
        else ensureHasType q(Int32) value
      mkAppM ``Oria.I32.lit #[value]
  | _ => throwError "object comparisons support I32 and Bool"

private def binary (f : Name) (a : ObjTy) (l r : Expr) : TermElabM Expr := do
  mkAppM f #[← operand a l, ← operand a r]

private def needsObject (types : List Expr) (expected : Option Expr) : TermElabM Bool := do
  if ← types.anyM (fun type => return (← objectCode? type).isSome) then return true
  if let some type := expected then
    if (← objectCode? (← instantiateMVars type)).isSome then return true
  if types.all (·.hasExprMVar) then tryPostpone
  return false

/-- Synthesize arithmetic before coercing its result into a host argument carrier.
Lean's operator helper leaves the result typeclass pending; synthesizing that application
first retains the numeric result needed by the ordinary coercion interface. A target with
its own arithmetic instance keeps Lean's expected-type-directed elaboration. -/
@[term_elab Lean.Parser.Term.binop]
def arithmetic : TermElab := fun stx expected => do
  let some target := expected | throwUnsupportedSyntax
  if target.hasExprMVar then throwUnsupportedSyntax
  if (← objectCode? target).isSome then throwUnsupportedSyntax
  let some f ← resolveId? stx[1] | throwUnsupportedSyntax
  unless f.getAppFn.constName? ∈
      [some ``HAdd.hAdd, some ``HSub.hSub, some ``HMul.hMul, some ``HDiv.hDiv] do
    throwUnsupportedSyntax
  let operation ← mkAppM f.getAppFn.constName!.getPrefix #[target, target, target]
  if (← trySynthInstance operation) matches .some _ then throwUnsupportedSyntax
  let saved ← saveState
  let value ← try withoutErrToSorry <| withSynthesize <| Lean.Elab.Term.Op.elabOp stx none catch
    | .error _ _ => saved.restore; throwUnsupportedSyntax
    | ex => throw ex
  ensureHasType target value

/-- Select object relations from operand types; restore Lean's original state for host relations. -/
@[term_elab Lean.Parser.Term.binrel, term_elab Lean.Parser.Term.binrel_no_prop]
def relation : TermElab := fun stx expected => withSynthesizeLight do
  let some f ← resolveId? stx[1] | throwUnsupportedSyntax
  let name := f.getAppFn.constName?
  unless name ∈ [some ``LT.lt, some ``LE.le, some ``GT.gt, some ``GE.ge,
      some ``BEq.beq, some ``bne] do throwUnsupportedSyntax
  let saved ← saveState
  let host := do
    saved.restore
    Lean.Elab.Term.Op.elabBinRelCore (stx.isOfKind ``Lean.Parser.Term.binrel_no_prop) stx expected
  let l ← try withoutErrToSorry <| elabTerm stx[2] none catch
    | .error _ _ => return ← host
    | ex => throw ex
  let lt ← instantiateMVars (← inferType l)
  if (← objectCode? lt).isNone && !lt.hasExprMVar &&
      !(lt.isConstOf ``Nat || lt.isConstOf ``Int || lt.isConstOf ``Int32 || lt.isConstOf ``Bool) then
    return ← host
  let r ← try withoutErrToSorry <| elabTerm stx[3] none catch
    | .error _ _ => return ← host
    | ex => throw ex
  let rt ← instantiateMVars (← inferType r)
  if ← needsObject [lt, rt] expected then
    let result ← match name with
      | some ``LT.lt => binary ``Oria.I32.lt .i32 l r
      | some ``LE.le => binary ``Oria.I32.le .i32 l r
      | some ``GT.gt => binary ``Oria.I32.lt .i32 r l
      | some ``GE.ge => binary ``Oria.I32.le .i32 r l
      | _ => do
          let code := (← objectCode? lt).or (← objectCode? rt)
          let a ← match code with
            | some code =>
                let code ← whnf code
                if code.isConstOf ``ObjTy.bool then pure ObjTy.bool
                else if code.isConstOf ``ObjTy.i32 then pure ObjTy.i32
                else throwError "object equality supports I32 and Bool"
            | none => pure (if lt.isConstOf ``Bool || rt.isConstOf ``Bool then ObjTy.bool else ObjTy.i32)
          let value ← binary (if a == .bool then ``Oria.Bool.eq else ``Oria.I32.eq) a l r
          if name == some ``bne then mkAppM ``Oria.Bool.not #[value] else pure value
    ensureHasType expected result
  else
    host

private def logical (name : Name) (objectName : Name) (l r : Syntax)
    (expected : Option Expr) : TermElabM Expr := withSynthesizeLight do
  let l ← withoutErrToSorry <| elabTerm l none
  let r ← withoutErrToSorry <| elabTerm r none
  let lt ← instantiateMVars (← inferType l)
  let rt ← instantiateMVars (← inferType r)
  if ← needsObject [lt, rt] expected then
    ensureHasType expected (← binary objectName .bool l r)
  else
    elabAppArgs (mkConst name) #[] #[.expr l, .expr r] expected
      (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

syntax (name := boolAnd) "oria_and% " term:max term:max : term
syntax (name := boolOr) "oria_or% " term:max term:max : term
syntax (name := boolNot) "oria_not% " term:max : term

macro_rules
  | `($l && $r) => `(oria_and% $l $r)
  | `($l || $r) => `(oria_or% $l $r)
  | `(!$value) => `(oria_not% $value)

@[term_elab boolAnd]
def conjunction : TermElab := fun stx expected =>
  logical ``and ``Oria.Bool.and stx[1] stx[2] expected

@[term_elab boolOr]
def disjunction : TermElab := fun stx expected =>
  logical ``or ``Oria.Bool.or stx[1] stx[2] expected

@[term_elab boolNot]
def negation : TermElab := fun stx expected => withSynthesizeLight do
  let value ← withoutErrToSorry <| elabTerm stx[1] none
  let type ← instantiateMVars (← inferType value)
  if ← needsObject [type] expected then
    ensureHasType expected (← mkAppM ``Oria.Bool.not #[← operand .bool value])
  else
    elabAppArgs (mkConst ``not) #[] #[.expr value] expected
      (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

end Oria.Elab.Operators
