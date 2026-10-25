module

meta import Oria.Language.Builder
meta import Oria.Meta.ObjectDerive
meta import Lean.Elab.Term
meta import Qq.MetaM

namespace Oria.Elab.Program.Internal

open Lean Lean.Elab Lean.Elab.Term Lean.Meta
open Qq

/-- Fully applied source, object code, and `Object` evidence for one `Val` carrier. -/
private structure Carrier where
  source : Q(Type)
  code : Q(ObjTy)
  object : Q(Object $source $code)
  region : Q(Region) := q(Region.any)

/-- Fully applied `Prog` type view with its exact grade and value carrier. -/
private structure Computation extends Carrier where
  grade : Q(Grade)

/-- One constructor shape consumed by the private ordered pattern matrix. -/
private structure ConstructorView where
  name : Name
  fields : Array Carrier
  reference : Expr

/-- A closed view of the constructors available for one object discriminant. -/
private structure MatchFamily where
  constructors : Array ConstructorView

private meta def Carrier.toType (carrier : Carrier) : Q(Type) :=
  let ⟨source, code, object, region⟩ := carrier
  q(@Val $source $region $code $object)

private meta def Carrier.toComputationType (carrier : Carrier) (grade : Q(Grade)) : Q(Type) :=
  let ⟨source, code, object, region⟩ := carrier
  q(@Prog $grade $source $region $code $object)

private meta def Computation.toType (computation : Computation) : Expr :=
  computation.toCarrier.toComputationType computation.grade

private meta def Carrier.canViewAs (source target : Carrier) : MetaM Bool := do
  return (← isDefEq source.source target.source) &&
    (← isDefEq source.code target.code) &&
    ((← isDefEq source.region target.region) || (← isDefEq target.region q(Region.any)))

private meta def carrier? (type : Expr) : MetaM (Option Carrier) := do
  let type := (← withReducible <| whnf type).consumeMData
  let_expr Val source region code object := type | return none
  return some { source, code, object, region }

private meta def computation? (type : Expr) : MetaM (Option Computation) := do
  let type := (← withReducible <| whnf type).consumeMData
  let_expr Prog grade source region code object := type | return none
  return some { source, code, object, grade, region }

private meta def freshCarrier : TermElabM Carrier := do
  let source ← mkFreshExprMVarQ q(Type) (userName := `A)
  let code ← mkFreshExprMVarQ q(ObjTy) (userName := `a)
  let object ← mkInstMVar q(Object $source $code)
  return { source, code, object }

/-- Resolve a do carrier to `Val A`, assigning an open carrier metavariable when necessary. -/
private meta def ensureCarrier (type : Expr) : TermElabM Carrier := do
  let type ← instantiateMVars type
  if let some carrier ← carrier? type then
    return carrier
  if type.isMVar then
    let carrier ← freshCarrier
    unless ← isDefEq type carrier.toType do
      throwError "failed to infer the object value carried by Oria `do`"
    return carrier
  throwError "Oria `do` computations carry `Val A`, but found{indentExpr type}"

end Oria.Elab.Program.Internal
