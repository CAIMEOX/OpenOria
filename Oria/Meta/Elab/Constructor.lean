module

public meta import Oria.Meta.Elab.Program.Internal
public meta import Oria.Meta.Elab.Record
public meta import Oria.Meta.ObjectDerive
meta import all Oria.Meta.Elab.Program.Internal
public meta import Lean.Elab.App
public meta import Lean.Elab.Notation

public meta section

namespace Oria.Elab.Constructor

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

private def builder? (env : Environment) (name : Name) : Option Name :=
  match name with
  | ``_root_.Option.none => some ``Oria.Option.none
  | ``_root_.Option.some => some ``Oria.Option.some
  | _ => ObjectRegistry.builder? env name

private def unparen (stx : Syntax) : TermElabM Syntax :=
  if stx.isOfKind ``Lean.Parser.Term.paren then
    liftMacroM (Lean.Elab.Command.removeParentheses stx)
  else pure stx

private def resolve? (head : Syntax) (source? : Option Expr) : TermElabM (Option Name) := do
  let head ← unparen head
  match head with
  | `(.$id:ident) =>
    unless id.getId.isAtomic do return none
    let some source := source? | return none
    let source ← whnf source
    let .const owner _ := source.getAppFn | return none
    let some (.inductInfo info) := (← getEnv).find? owner | return none
    return info.ctors.find? (·.getString! == id.getId.getString!)
  | _ =>
    unless head.isIdent do return none
    let (_, resolutions) ← resolveName' head []
    match resolutions with
    | [(expr, _, [], _)] => pure expr.constName?
    | _ => pure none

/-- Elaborate a source constructor in an object computation position. An expected Prog
supplies the datatype for leading-dot syntax. Ordinary actions retain their synthesis path.
Lean's application elaborator checks fields, named arguments, and implicit parameters. -/
def elaborate? (stx : Syntax) (expected? : Option Expr) : TermElabM (Option Expr) := do
  let saved ← saveState
  let skip := do saved.restore; pure none
  let stx ← unparen stx
  if let some result ← Record.elaborate? stx expected? then return some result
  let (head, named, args, ellipsis) ←
    if stx.isOfKind ``Lean.Parser.Term.app then expandApp stx
    else pure (stx, #[], #[], false)
  let source? ← match expected? with
    | none => pure none
    | some type => (Program.Internal.computation? type) <&> fun type => type.map (·.source)
  let some name ← resolve? head source? | skip
  let some builder := builder? (← getEnv) name | skip
  let fn ← mkConstWithFreshMVarLevels builder
  let result ← withRef stx <| elabAppArgs fn named args expected?
    (explicit := false) (ellipsis := ellipsis)
  unless (← Program.Internal.computation? (← inferType result)).isSome do
    throwErrorAt stx "an object constructor must be fully applied"
  addConstInfo head name
  return some result

/-- Expected object computation types select constructor builders; host terms use Lean. -/
@[term_elab ident, term_elab Lean.Parser.Term.dotIdent, term_elab Lean.Parser.Term.app]
def elaborate : TermElab := fun stx expected? => do
  let some expected := expected? | throwUnsupportedSyntax
  unless (← Program.Internal.computation? expected).isSome do throwUnsupportedSyntax
  let some result ← elaborate? stx expected? | throwUnsupportedSyntax
  return result

end Oria.Elab.Constructor
