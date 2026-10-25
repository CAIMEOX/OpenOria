module

public import Oria.Language.Persistent
public import Oria.Language.Control
public meta import Lean.Elab.Do.Basic
public meta import Oria.Meta.Elab.Program.Internal
public meta import Oria.Meta.Elab.Constructor
public meta import Oria.Meta.Elab.NbtAccess
meta import all Oria.Meta.Elab.Program.Internal
meta import Lean.Elab.BuiltinDo
public meta import Qq.MetaM
public meta import Lean.Meta.Tactic.Simp.Main

public section

namespace Oria.Elab.ProgDo

open Lean Lean.Elab Lean.Elab.Term Lean.Meta
open Lean.Parser.Term
open Qq

private abbrev Carrier := Program.Internal.Carrier

private meta def mkValuePure (carrierTy value : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let carrier ← Program.Internal.ensureCarrier carrierTy
  let ⟨source, code, object, region⟩ := carrier
  let value : Q(@Val $source $region $code $object) ← ensureHasType carrier.toType value
  return q(Prog.pure $value)

private meta def mkValueComputation (carrierType : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let carrier ← Program.Internal.ensureCarrier carrierType
  let grade ← mkFreshExprMVar (mkConst ``Oria.Grade) (userName := `g)
  return carrier.toComputationType grade

private meta def mkValueBind
    (leftCarrier rightCarrier program next : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let left ← Program.Internal.ensureCarrier leftCarrier
  let right ← Program.Internal.ensureCarrier rightCarrier
  let some programType ← Program.Internal.computation? (← inferType program)
    | throwError "the left side of an Oria `do` bind must be a `Prog` computation"
  unless ← isDefEq left.toType programType.toCarrier.toType do
    throwError "the left side of an Oria `do` bind returns an incompatible object value"
  let (parameters, _, bodyType) ← forallMetaTelescopeReducing (← inferType next)
  unless parameters.size == 1 do
    throwError "internal Oria `do` continuation has an invalid arity"
  let some nextType ← Program.Internal.computation? bodyType
    | throwError "the continuation of an Oria `do` bind must return a `Prog` computation"
  unless ← isDefEq right.toType nextType.toCarrier.toType do
    throwError "the continuation of an Oria `do` bind returns an incompatible object value"
  let ⟨A, a, objectA, r⟩ := left
  let ⟨B, b, objectB, q⟩ := right
  let g := programType.grade
  let h := nextType.grade
  let program : Q(@Prog $g $A $r $a $objectA) := program
  let next : Q(@Val $A $r $a $objectA → @Prog $h $B $q $b $objectB) := next
  return q(Prog.bind $program $next)

private meta def pureArgument? (expression : Expr) : Option Expr := do
  let_expr Oria.Prog.pure _ _ _ _ value := expression.consumeMData | none
  return value

private meta def splitValueComputation?
    (type : Expr) : TermElabM (Option (Lean.Elab.Do.MonadInfo × Expr)) := do
  let some computation ← Program.Internal.computation? type | return none
  let carrier := computation.toCarrier.toType
  let family := Expr.lam `valueType (mkSort 1) type .default
  return some ({ m := family, u := 0, v := 0 }, carrier)

private meta def operations : Lean.Elab.Do.DoOps := {
  mkPureApp := mkValuePure
  mkBindApp := mkValueBind
  isPureApp? := pureArgument?
  splitMonadApp? := splitValueComputation?
  mkMonadApp := mkValueComputation
}

private meta def primitiveCarrier
    (sourceName objectName : Name) : TermElabM Carrier := do
  let source : Q(Type) := mkConst sourceName
  let code : Q(ObjTy) := mkConst objectName
  let object ← mkInstMVar q(Object $source $code)
  return { source, code, object }

private meta def unitCarrier : TermElabM Carrier :=
  primitiveCarrier ``Unit ``Oria.ObjTy.unit

private meta def boolCarrier : TermElabM Carrier :=
  primitiveCarrier ``Bool ``Oria.ObjTy.bool

private meta def mkBranch
    (condition yes no : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let some yesType ← Program.Internal.computation? (← inferType yes)
    | throwError "the `then` branch of an object `if` must be a `Prog` computation"
  let some noType ← Program.Internal.computation? (← inferType no)
    | throwError "the `else` branch of an object `if` must be a `Prog` computation"
  unless ← isDefEq
      yesType.toCarrier.toType
      noType.toCarrier.toType do
    throwError "object `if` branches return incompatible value types"
  let ⟨source, code, object, region⟩ := yesType.toCarrier
  let g := yesType.grade
  let h := noType.grade
  let condition : Q(Val Bool) := condition
  let yes : Q(@Prog $g $source $region $code $object) := yes
  let no : Q(@Prog $h $source $region $code $object) := no
  return q(Prog.branch $condition $yes $no)

private meta def mkHostIf
    (condition : Expr)
    (yes no : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let some yesType ← Program.Internal.computation? (← inferType yes) | throwUnsupportedSyntax
  let some noType ← Program.Internal.computation? (← inferType no) | throwUnsupportedSyntax
  unless ← isDefEq yesType.toCarrier.toType noType.toCarrier.toType do
    throwError "host `if` branches produce incompatible object values"
  let (yes, no) ← if ← isDefEq yesType.grade noType.grade then pure (yes, no)
    else do
      let left ← mkAppM ``Grade.below_join_left #[yesType.grade, noType.grade]
      let right ← mkAppM ``Grade.below_join_right #[yesType.grade, noType.grade]
      pure (← mkAppM ``Prog.weaken #[yes, left], ← mkAppM ``Prog.weaken #[no, right])
  let expected ← inferType yes
  Lean.Elab.Do.doElabToSyntax "condition of host `if`" (pure condition) fun condition =>
  Lean.Elab.Do.doElabToSyntax "then branch of host `if`" (pure yes) fun yes =>
  Lean.Elab.Do.doElabToSyntax "else branch of host `if`" (pure no) fun no => do
    Term.elabTermEnsuringType
      (← `(if $condition then $yes else $no))
      expected

private meta def unsupported
    (stx : Syntax) (description : String) : TermElabM Unit :=
  throwErrorAt stx "Oria `do` does not support {description}"

private meta def checkLetConfig (configSyntax : TSyntax ``letConfig) : TermElabM Unit := do
  let config ← Term.mkLetConfig configSyntax {}
  if config.nondep || config.usedOnly || config.zeta || config.postponeValue ||
      config.generalize || config.eq?.isSome then
    unsupported configSyntax "configured `let` bindings"

private meta def checkIf
    (condition : TSyntax ``doIfCond)
    (yes no : TSyntax ``doSeq) : TermElabM (Array (TSyntax ``doSeq)) := do
  match condition with
  | `(doIfCond| $_:term) => pure ()
  | `(doIfCond| $_:ident : $_:term) =>
      throwErrorAt condition "Oria `do` does not support dependent `if`"
  | _ =>
      throwErrorAt condition
        "Oria `do` supports only a plain condition in `if`; use explicit object elimination for pattern tests"
  return #[yes, no]

private meta def checkMatch
    (alts : Array (TSyntax ``matchAlt)) : TermElabM (Array (TSyntax ``doSeq)) := do
  let mut branches := #[]
  for alt in alts do
    let some view := Term.getMatchAlt ``doSeq alt
      | throwErrorAt alt "Oria `do` does not support this `match` alternative"
    branches := branches.push view.rhs
  return branches

private meta def rejectUnsupportedKind
    (stx : TSyntax `doElem) : TermElabM (Array (TSyntax ``doSeq)) := do
  let kind := stx.raw.getKind
  if kind == ``Lean.Parser.Term.doFor ||
      kind == ``Lean.Parser.Term.doRepeat ||
      kind == ``Lean.Parser.Term.doWhile ||
      kind == ``Lean.Parser.Term.doRepeatUntil ||
      kind == ``Lean.Parser.Term.doUnless then
    unsupported stx "loops"
  else if kind == ``Lean.Parser.Term.doTry then
    throwErrorAt stx "Oria failure recovery uses one `catch _ =>` arm"
  else if kind == ``Lean.Parser.Term.doBreak ||
      kind == ``Lean.Parser.Term.doContinue then
    unsupported stx "`break` or `continue`"
  else if kind == ``Lean.Parser.Term.doReassign ||
      kind == ``Lean.Parser.Term.doReassignArrow then
    unsupported stx "reassignment"
  else
    unsupported stx "this do element"
  return #[]

private meta def checkElement
    (stx : TSyntax `doElem)
    (isLast : Bool) : TermElabM (Array (TSyntax ``doSeq)) := do
  match stx with
  | `(doReturn| return $[$_]?) =>
      return #[]
  | `(doElem| skip) => return #[]
  | `(doTry| try $body catch _ => $handler) => return #[body, handler]
  | `(doExpr| $_:term) =>
      return #[]
  | `(doReassign| $_:ident := $_:term) => return #[]
  | `(doReassign| $_:letPatDecl) => return #[]
  | `(doLetArrow| let%$_ $[mut%$mutTk?]? $syntaxConfig:letConfig $decl) =>
      if mutTk?.isSome then
        unsupported stx "mutable bindings"
      checkLetConfig syntaxConfig
      match decl with
      | `(doIdDecl| $_:ident $[: $_]? ← $_)
      | `(doPatDecl| _%$_ $[: $_]? ← $_) =>
          if isLast then throwErrorAt stx "Oria `do` must end with `return` or a `Prog` expression"
          return #[]
      | `(doPatDecl| $_ $[: $_]? ← $_ $[| $otherwise $[$body]?]?) =>
          if isLast && body.join.isNone then
            throwErrorAt stx "Oria `do` must end with `return` or a `Prog` expression"
          return (otherwise.map (fun s => (⟨s.raw⟩ : TSyntax ``doSeq))).toArray ++
            (body.join.map (fun s => (⟨s.raw⟩ : TSyntax ``doSeq))).toArray
      | _ =>
          unsupported stx "pattern bindings after `←`"
          return #[]
  | `(doLet| let%$_ $[mut%$mutTk?]? $syntaxConfig:letConfig $_:letDecl) =>
      if isLast then
        throwErrorAt stx "Oria `do` must end with `return` or a `Prog` expression"
      if mutTk?.isSome then
        unsupported stx "mutable bindings"
      checkLetConfig syntaxConfig
      return #[]
  | `(doLetRec| let rec $_:letRecDecls) =>
      if isLast then
        throwErrorAt stx "Oria `do` must end with `return` or a `Prog` expression"
      return #[]
  | `(doLetElse| let $[mut]? $config:letConfig $_ := $_ | $otherwise $[$body]?) =>
      checkLetConfig config
      return #[⟨otherwise.raw⟩] ++ (body.map (fun s => (⟨s.raw⟩ : TSyntax ``doSeq))).toArray
  | `(doFor| for $[$[$_ :]? $_ in $_],* do $body) => return #[body]
  | `(doElem| break) | `(doElem| continue) => return #[]
  | `(doIf| if $condition:doIfCond then $yes else $no) =>
      checkIf condition yes no
  | `(doIf| if $condition:doIfCond then $yes
      $[else if $conditions:doIfCond then $branches]* $[else $no]?) => do
      let empty ← `(doSeq| skip)
      discard <| checkIf condition yes (no.getD empty)
      for (condition, branch) in conditions.zip branches do
        discard <| checkIf condition branch empty
      return #[yes] ++ branches ++ no.toArray
  | `(doMatch| match $[(dependent := $_)]? $[(generalizing := $_)]? $(_)?
      $_,* with $alts:matchAlt*) =>
      checkMatch alts
  | _ =>
      rejectUnsupportedKind stx

/-- Lean scans `:=` as host pattern reassignment. Oria assignments have one normal
control exit; their storage effects and Failure are checked during elaboration.
Only the control scan uses this view. The original syntax is elaborated below. -/
private meta def controlInfo (sequence : TSyntax ``doSeq) : TermElabM Lean.Elab.Do.ControlInfo := do
  let skip ← `(doElem| skip)
  let view ← sequence.raw.replaceM fun stx =>
    pure <| if stx.isOfKind ``Lean.Parser.Term.doReassign then some skip.raw else none
  Lean.Elab.Do.inferControlInfoSeq ⟨view⟩

private meta def checkSequence (root : TSyntax ``doSeq) : TermElabM Bool := do
  let mut pending := #[root]
  let mut needsExit := false
  while let some sequence := pending.back? do
    pending := pending.pop
    let elements := Lean.Parser.Term.getDoElems sequence
    for index in [:elements.size] do
      let isLast := index + 1 == elements.size
      let branches ← checkElement elements[index]! isLast
      if elements[index]!.raw.isOfKind ``Lean.Parser.Term.doFor then
        for branch in branches do
          let info ← controlInfo branch
          if info.returnsEarly then needsExit := true
      unless isLast do
        if elements[index]!.raw.isOfKind ``Lean.Parser.Term.doReturn then needsExit := true
        for branch in branches do
          let info ← controlInfo branch
          if info.returnsEarly then
            needsExit := true
      pending := pending ++ branches
  return needsExit

private meta def inProgDo : Lean.Elab.Do.DoElabM Bool := do
  let computation ← Lean.Elab.Do.mkMonadApp (← read).doBlockResultType
  return (← Program.Internal.computation? computation).isSome

private meta def actionTerm
    (action : TSyntax `doElem) : Lean.Elab.Do.DoElabM (TSyntax `term) := do
  match action with
  | `(doElem| $term:term) => return term
  | _ => throwUnsupportedSyntax

private meta def bindAction
    (binder : Carrier)
    (program next : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType next)
  let some answer ← Program.Internal.computation? type
    | throwError "an Oria `do` continuation must return a `Prog` computation"
  mkValueBind binder.toType answer.toCarrier.toType program next

private meta def normalizeGrade (g : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext (simpTheorems := #[← getSimpTheorems])
    (config := { autoUnfold := true })
  let methods := Simp.mkDefaultMethodsCore #[← Simp.getSimprocs]
  -- Preserve interface rewrites and let simp construct the proof from the original grade.
  -- Only unfold grade, context, and row helpers; keep numeric literals intact.
  let post := methods.post >> fun e => do
    if e.isAppOf ``OfNat.ofNat then return .continue
    let ty ← whnf (← inferType e)
    unless ty.isConstOf ``Grade || ty.isConstOf ``ContextChange || ty.isAppOf ``BitVec do
      return .continue
    let reduced ← withTransparency .default <| whnf e
    if reduced == e then return .continue
    return .visit { expr := reduced }
  return (← Simp.mainCore g ctx (methods := { methods with post })).1

private meta def rowDocument (n : Nat) (names : List (Nat × String)) : Std.Format :=
  let labels := names.filterMap fun (bit, name) =>
    if n &&& bit != 0 then some (Std.Format.text name) else none
  Std.Format.group <| "{" ++ Std.Format.joinSep labels ("," ++ Std.Format.line) ++ "}"

private meta def gradeDocument? (g : Expr) : TermElabM (Option Std.Format) := do
  let req ← mkAppM ``BitVec.toNat #[mkProj ``Grade 0 g]
  let eff ← mkAppM ``BitVec.toNat #[mkProj ``Grade 1 g]
  let some req ← getNatValue? (← withTransparency .all <| whnf req) | return none
  let some eff ← getNatValue? (← withTransparency .all <| whnf eff) | return none
  let required := rowDocument req [
    (1, "executor"), (2, "position"), (4, "rotation"), (8, "dimension"), (16, "anchor")]
  let effects := rowDocument eff [
    (1, "world"), (2, "scoreboardRead"), (4, "scoreboardWrite"), (8, "persistentRead"),
    (16, "persistentWrite"), (32, "persistentAlloc"), (64, "random"), (128, "chat"),
    (256, "dialog"), (512, "sound"), (1024, "hud"), (2048, "failure"), (4096, "suspend"),
    (8192, "memoryRead"), (16384, "memoryWrite")]
  return some (Std.Format.group <| "requires " ++ required ++ Std.Format.line ++ "effects " ++ effects)

/-- Normalize a computation's static annotation before it enters a dependent continuation. -/
private meta def normalizeComputation (body : Expr) : TermElabM Expr := do
  let some actual ← Program.Internal.computation? (← inferType body) | return body
  let normal ← normalizeGrade actual.grade
  if normal.expr.hasExprMVar then return body
  let family ← withLocalDeclD `g (mkConst ``Oria.Grade) fun g =>
    mkLambdaFVars #[g] (actual.toCarrier.toComputationType g)
  mkEqMP (← mkCongrArg family (← normal.getProof)) body

private meta def withBinder
    (binder : Carrier)
    (name : Name)
    (ref : Syntax)
    (program : Expr)
    (dec : Lean.Elab.Do.DoElemCont) : Lean.Elab.Do.DoElabM Expr := do
  let dec ← dec.ensureUnitAt ref
  let program ← normalizeComputation program
  withLocalDecl name .default binder.toType fun value => do
    Term.addLocalVarInfo (mkIdentFrom ref name) value
    let next ← normalizeComputation (← dec.continueWithUnit)
    let next ← mkLambdaFVars #[value] next
    bindAction binder program next

private meta def selectBinding
    (programType : Program.Internal.Computation)
    (annotation? : Option Carrier) :
    Lean.Elab.Do.DoElabM Carrier := do
  match annotation? with
  | none => return programType.toCarrier
  | some carrier =>
      unless ← programType.toCarrier.canViewAs carrier do
        throwError "Oria `do` binder annotation does not match the action result"
      return carrier

private meta def elaborateBinding
    (name : Name)
    (ref : Syntax)
    (annotation? : Option (TSyntax `term))
    (action : TSyntax `doElem)
    (dec : Lean.Elab.Do.DoElemCont) : Lean.Elab.Do.DoElabM Expr := do
  let (program, binder) ← Term.withSynthesize (postpone := .partial) do
    let action ← actionTerm action
    let annotation? ← annotation?.mapM fun annotation => do
      let type ← Term.elabType annotation
      let some carrier ← Program.Internal.carrier? type
        | throwErrorAt annotation "an Oria `do` binder annotation must have type `Val A`"
      pure carrier
    let constructor? ← match ← NbtAccess.read? action with
      | some action => pure (some action)
      | none => Constructor.elaborate? action none
    let constructor? ← match constructor?, annotation? with
      | none, some carrier => Constructor.elaborate? action (some (carrier.toComputationType q(Grade.pure)))
      | _, _ => pure constructor?
    if constructor?.isNone && annotation?.isNone then
      let head := if action.raw.isOfKind ``Lean.Parser.Term.app then action.raw[0] else action.raw
      if head.isOfKind ``Lean.Parser.Term.dotIdent then
        throwErrorAt action
          "a leading-dot object constructor needs a datatype; annotate the binder as `Val A` or use `A.constructor`"
    let value ← match constructor? with
      | some value => pure value
      | none => Term.withSynthesize (postpone := .partial) (Term.elabTerm action none)
    let type ← whnf (← inferType value)
    let program ←
      if type.isAppOfArity ``Oria.Persistent.Root 3 then
        mkAppM ``Oria.Persistent.Root.get #[value]
      else pure value
    let some programType ← Program.Internal.computation? (← inferType program)
      | throwErrorAt action "the right side of an Oria `do` bind must be a `Prog`"
    let binder ← selectBinding programType annotation?
    let program ← ensureHasType (binder.toComputationType programType.grade) program
    pure (program, binder)
  withBinder binder name ref program dec

/-- A pure object let names one Tree value; host values and program descriptions
retain Lean's let elaboration. -/
@[doElem_elab Lean.Parser.Term.doLet]
public meta def elaborateLet : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doLet| let%$_ $[mut%$_]? $config:letConfig $decl:letDecl) := stx
    | throwUnsupportedSyntax
  let `(letDecl| $decl:letIdDecl) := decl | throwUnsupportedSyntax
  let view := Term.mkLetIdDeclView decl
  unless view.binders.isEmpty do throwUnsupportedSyntax
  checkLetConfig config
  let saved ← saveState
  let value ← try Term.withoutErrToSorry <| Term.withSynthesize (postpone := .partial) do
    let type ← Term.elabType view.type
    Term.elabTermEnsuringType view.value type
  catch
    | .error .. => saved.restore; throwUnsupportedSyntax
    | ex => throw ex
  let some carrier ← Program.Internal.carrier? (← instantiateMVars (← inferType value))
    | saved.restore; throwUnsupportedSyntax
  let program ← mkAppM ``Oria.Prog.pure #[value]
  let name ← if view.id.isIdent then pure view.id else Term.mkFreshIdent view.id (canonical := true)
  withBinder carrier name.getId name program dec

/-- Fully annotated local functions over object values use the object fixpoint.
Host recursive functions retain Lean's recursion and termination checking. -/
@[doElem_elab Lean.Parser.Term.doLetRec]
public meta def elaborateRec : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doLetRec| let rec $decls:letRecDecls) := stx | throwUnsupportedSyntax
  let saved ← saveState
  let mut candidates := #[]
  for declaration in decls.raw[0].getSepArgs do
    let `(letDecl| $decl:letIdDecl) := declaration[2] | saved.restore; throwUnsupportedSyntax
    let view := Term.mkLetIdDeclView decl
    let type ← Term.elabBindersEx view.binders fun xs => do
      let result ← Term.elabType view.type
      mkForallFVars (xs.map (·.2)) result
    let object ← forallTelescopeReducing type fun xs result => do
      if (← Program.Internal.computation? result).isNone then return false
      xs.allM fun x => return (← Program.Internal.carrier? (← inferType x)).isSome
    candidates := candidates.push (declaration, view, type, object)
  unless candidates.any (·.2.2.2) do saved.restore; throwUnsupportedSyntax
  unless candidates.size == 1 do
    throwErrorAt stx "an Oria runtime `let rec` binds one function"
  let some (declaration, view, type, _) := candidates[0]?
    | throwErrorAt stx "missing runtime recursive declaration"
  unless declaration[1].isNone && declaration[3].getArgs.all Syntax.isNone do
    throwErrorAt declaration "runtime recursion uses a function type and body; attributes and termination hints belong to host recursion"
  if (← instantiateMVars type).hasExprMVar then
    throwErrorAt view.id "a runtime recursive function requires explicit parameter, result, and grade annotations"
  let binders := view.binders.map (fun b => (⟨b⟩ : TSyntax ``Lean.Parser.Term.funBinder))
  let value : Term := ⟨view.value⟩
  let rhs ← if binders.isEmpty then pure value else `(fun $binders* => $value)
  let action ← withLocalDeclD view.id.getId type fun recur => do
    Term.addLocalVarInfo view.id recur
    let body ← Term.elabTermEnsuringType rhs type
    mkAppM ``Prog.fix #[← mkLambdaFVars #[recur] body]
  let dec ← dec.ensureUnitAt view.id
  withLetDecl view.id.getId type action fun value => do
    Term.addLocalVarInfo view.id value
    mkLetFVars #[value] (← dec.continueWithUnit)

@[doElem_elab Lean.Parser.Term.doReturn]
public meta def elaborateReturn : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doReturn| return $value) := stx | throwUnsupportedSyntax
  let continuation ← Lean.Elab.Do.getReturnCont
  let carrier ← Program.Internal.ensureCarrier continuation.resultType
  let expected := carrier.toComputationType q(Grade.pure)
  let some program ← Constructor.elaborate? value (some expected) | throwUnsupportedSyntax
  dec.elabAsSyntacticallyDeadCode
  withLocalDeclD `constructed carrier.toType fun result => do
    let body ← continuation.k result
    let next ← mkLambdaFVars #[result] body
    mkAppM ``Oria.Prog.bind #[program, next]

@[doElem_elab Lean.Parser.Term.doLetArrow]
public meta def elaborateLetArrow : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doLetArrow| let%$_ $[mut%$_]? $syntaxConfig:letConfig $decl) := stx
    | throwUnsupportedSyntax
  checkLetConfig syntaxConfig
  match decl with
  | `(doIdDecl| $name:ident $[: $annotation?]? ← $action) =>
      elaborateBinding name.getId name annotation? action dec
  | `(doPatDecl| _%$wildcard $[: $annotation?]? ← $action) =>
      elaborateBinding `ignored wildcard annotation? action dec
  | _ => throwUnsupportedSyntax

private meta def finishStatement (action : Syntax) (build : TermElabM Expr)
    (dec : Lean.Elab.Do.DoElemCont) : Lean.Elab.Do.DoElabM Expr := do
  let punit ← Lean.Elab.Do.mkPUnit
  let unit ← unitCarrier
  let original := dec
  let tailUnit ← match ← Program.Internal.carrier? dec.resultType with
    | some carrier => do
        let source ← whnf carrier.source
        if source.hasExprMVar then pure false else isDefEq source q(Unit)
    | none => pure false
  let dec ← if tailUnit then
      let resultName ← mkFreshUserName `unitStatement
      let next : Lean.Elab.Do.DoElemCont := {
        resultName
        resultType := punit
        k := Lean.Elab.Do.mkPureApp unit.toType (mkConst ``Val.unit)
      }
      pure next
    else pure dec
  unless ← isDefEq dec.resultType punit do throwUnsupportedSyntax
  let program ← Term.withSynthesize (postpone := .partial) build
  let some programType ← Program.Internal.computation? (← inferType program)
    | throwErrorAt action "an Oria `do` statement must be a `Prog` computation"
  if tailUnit then
    let expected ← Lean.Elab.Do.mkMonadApp unit.toType
    if ← isDefEq (← inferType program) expected then
      return ← original.mkBindUnlessPure program
  withBinder programType.toCarrier `ignored action program dec

@[doElem_elab Lean.Parser.Term.doExpr]
public meta def elaborateStatement : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doExpr| $action:term) := stx | throwUnsupportedSyntax
  finishStatement action (Term.elabTerm action none) dec

@[doElem_elab Lean.Parser.Term.doReassign]
public meta def elaborateRootAssignment : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let (root, value) ← match stx with
    | `(doReassign| $root:ident := $value:term) => pure ((⟨root.raw⟩ : Term), value)
    | `(doReassign| $decl:letPatDecl) =>
        let decl : TSyntax ``letDecl := ⟨mkNode ``letDecl #[decl.raw]⟩
        let `(letDecl| $root:term := $value:term) := decl | throwUnsupportedSyntax
        pure (root, value)
    | _ => throwUnsupportedSyntax
  let program ← match ← NbtAccess.write? root value with
    | some program => pure program
    | none => Term.elabTerm (← `(Oria.Persistent.Root.set $root $value)) none
  if let some result ← Program.Internal.carrier? dec.resultType then
    unless ← isDefEq result.source q(Unit) do
      throwErrorAt stx "assignment produces Unit; return a value to finish this block"
  finishStatement stx (pure program) dec

private meta def elaborateBranch
    (sequence : TSyntax ``doSeq)
    (carrier : Carrier) : Lean.Elab.Do.DoElabM Expr := do
  let continuation ← Lean.Elab.Do.DoElemCont.mkPure carrier.toType
  Lean.Elab.Do.withDoBlockResultType carrier.toType <|
    Lean.Elab.Do.elabDoSeq sequence continuation

private meta def bindUnitBranch
    (dec : Lean.Elab.Do.DoElemCont)
    (branch : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let unit ← unitCarrier
  let next ← dec.continueWithUnit
  withLocalDecl `ignored .default unit.toType fun ignored => do
    let continuation ← mkLambdaFVars #[ignored] next
    Lean.Elab.Do.mkBindApp
      unit.toType
      (← read).doBlockResultType
      branch
      continuation

@[doElem_elab Lean.Parser.Term.InternalSyntax.doSkip]
public meta def elaborateSkip : Lean.Elab.Do.DoElab := fun _ dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let unit ← unitCarrier
  let program ← Lean.Elab.Do.mkPureApp unit.toType (mkConst ``Val.unit)
  if (← Program.Internal.carrier? dec.resultType).isSome then
    dec.mkBindUnlessPure program
  else bindUnitBranch dec program

private meta def emitExit (target value : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let program ← Lean.Elab.Do.mkPureApp (← inferType value) value
  let some left ← Program.Internal.computation? (← inferType program)
    | throwError "an object return must produce a Prog computation"
  let some right ← Program.Internal.computation?
      (← Lean.Elab.Do.mkMonadApp (← read).doBlockResultType)
    | throwError "an object return requires an object continuation"
  let ⟨A, a, objectA, r⟩ := left.toCarrier
  let ⟨B, b, objectB, q⟩ := right.toCarrier
  have target : Q(@Control.Internal.Target $A $r $a $objectA) := target
  withLocalDeclD `returned left.toCarrier.toType fun result => do
    have result : Q(@Val $A $r $a $objectA) := result
    let exit := q(@Control.Internal.leave $A $B $r $q $a $b $objectA $objectB $target $result)
    let next ← mkLambdaFVars #[result] exit
    mkAppM ``Prog.bind #[program, next]

@[doElem_elab Lean.Parser.Term.doFor]
public meta def elaborateFor : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doFor| for $[$[$membership :]? $names in $collections],* do $body) := stx
    | throwUnsupportedSyntax
  unless names.size == 1 && (membership[0]?.join).isNone do
    throwErrorAt stx "an object `for` takes one finite host collection"
  let name := names[0]!
  unless name.isIdent || name.isOfKind ``Lean.Parser.Term.hole do
    throwErrorAt name "an object `for` binder must be an identifier or `_`"
  let values ← Term.elabTerm collections[0]! none
  let type ← whnf (← inferType values)
  let values ← if type.isAppOf ``Array then mkAppM ``Array.toList #[values]
    else match type.getAppFn.constName? with
      | some ``Std.Rco => mkAppM ``Std.Rco.toList #[values]
      | some ``Std.Rcc => mkAppM ``Std.Rcc.toList #[values]
      | some ``Std.Roc => mkAppM ``Std.Roc.toList #[values]
      | some ``Std.Roo => mkAppM ``Std.Roo.toList #[values]
      | _ => pure values
  let_expr List element := (← whnf (← inferType values))
    | throwErrorAt stx "an object `for` iterates a host List, Array, or range"
  let unit ← unitCarrier
  let ⟨A, a, object, r⟩ := unit
  let info ← controlInfo body
  let targetType := q(@Control.Internal.Target $A $r $a $object)
  let loop ← withLocalDeclD `breakTarget targetType fun breakTarget => do
    let loopBody ← withLocalDeclD
        (if name.isIdent then name.getId else `ignored) element fun value => do
      let iteration ← withLocalDeclD `continueTarget targetType fun continueTarget => do
        let returnCont ← Lean.Elab.Do.getReturnCont
        let continuation ← Lean.Elab.Do.DoElemCont.mkPure unit.toType
        let action ← Lean.Elab.Do.withDoBlockResultType unit.toType <|
          Lean.Elab.Do.enterLoopBody
            (emitExit breakTarget (mkConst ``Val.unit))
            (emitExit continueTarget (mkConst ``Val.unit)) returnCont <|
            Lean.Elab.Do.elabDoSeq body continuation
        let action ← normalizeComputation action
        if info.continues then
          mkAppM ``Control.Internal.block #[← mkLambdaFVars #[continueTarget] action]
        else pure action
      mkLambdaFVars #[value] iteration
    let loop ← mkAppM ``Control.Internal.forList #[values, loopBody]
    if info.breaks then mkAppM ``Control.Internal.block #[← mkLambdaFVars #[breakTarget] loop]
    else pure loop
  finishStatement stx (pure loop) dec

private meta def elaborateBlock (sequence : TSyntax ``doSeq)
    (expected : Expr) (carrier : Carrier) : TermElabM Expr := do
  let ⟨A, a, objectA, r⟩ := carrier
  withLocalDeclD `returnTarget q(@Control.Internal.Target $A $r $a $objectA) fun target => do
    let ctx ← Lean.Elab.Do.mkContext (some expected) operations
    let contInfo : Lean.Elab.Do.ContInfo := {
      returnCont := { resultType := ctx.doBlockResultType, k := emitExit target }
    }
    let ctx := { ctx with contInfo := contInfo.toContInfoRef }
    let continuation ← Lean.Elab.Do.DoElemCont.mkPure ctx.doBlockResultType
    let body ← (Lean.Elab.Do.elabDoSeq sequence continuation).run ctx
    let body ← mkLambdaFVars #[target] body
    mkAppM ``Control.Internal.block #[body]

@[doElem_elab Lean.Parser.Term.doIf]
public meta def elaborateIf : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doIf| if $conditionSyntax:doIfCond then $yes else $no) := stx
    | throwUnsupportedSyntax
  let conditionSyntax ← match conditionSyntax with
    | `(doIfCond| $condition:term) => pure condition
    | _ => throwUnsupportedSyntax
  let condition ← Term.elabTerm conditionSyntax none
  let conditionType ← instantiateMVars (← inferType condition)
  if conditionType.hasMVar then
    throwErrorAt conditionSyntax
      "Oria `do` cannot infer the `if` condition type; add a `Bool`, `Prop`, or `Val Bool` annotation"
  let bool ← boolCarrier
  let isObject ← match ← Program.Internal.carrier? conditionType with
    | some carrier => carrier.canViewAs bool
    | none => pure false
  let isHost ← if isObject then
    pure false
  else do
    let isBool ← isDefEq conditionType (mkConst ``Bool)
    let isProposition ← isProp condition
    pure (isBool || isProposition)
  unless isObject || isHost do
    throwErrorAt conditionSyntax
      "Oria `do` `if` condition must have type `Bool`, `Prop`, or `Val Bool`"
  let condition ← if isObject then ensureHasType bool.toType condition else pure condition
  let resultCarrier? ← Program.Internal.carrier? dec.resultType
  match resultCarrier? with
  | some resultCarrier =>
      let yes ← elaborateBranch yes resultCarrier
      let no ← elaborateBranch no resultCarrier
      let branch ← if isObject then
        mkBranch condition yes no
      else
        mkHostIf condition yes no
      dec.mkBindUnlessPure branch
  | none =>
      let expectedUnit ← Lean.Elab.Do.mkPUnit
      unless ← isDefEq dec.resultType expectedUnit do
        throwError "object `if` appears in an unsupported dependent continuation"
      let unit ← unitCarrier
      let yes ← elaborateBranch yes unit
      let no ← elaborateBranch no unit
      let branch ← if isObject then
        mkBranch condition yes no
      else
        mkHostIf condition yes no
      bindUnitBranch dec branch

@[doElem_elab Lean.Parser.Term.doTry]
public meta def elaborateTry : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doTry| try $body catch _ => $handler) := stx
    | throwErrorAt stx "Oria failure recovery uses `catch _ =>`"
  let carrier? ← Program.Internal.carrier? dec.resultType
  let carrier ← match carrier? with
    | some carrier => pure carrier
    | none => unitCarrier
  let body ← elaborateBranch body carrier
  let handler ← elaborateBranch handler carrier
  let action ← mkAppM ``Oria.Prog.catchFailure #[body, handler]
  match carrier? with
  | some _ => dec.mkBindUnlessPure action
  | none => bindUnitBranch dec action

private meta def elaborateSequence
    (sequence : TSyntax ``doSeq)
    (expectedType : Expr) : TermElabM Expr := do
  Term.tryPostponeIfMVar expectedType
  let expectedType ← instantiateMVars expectedType
  match ← Program.Internal.computation? expectedType with
  | none => throwUnsupportedSyntax
  | some computation =>
      let needsExit ← checkSequence sequence
      let grade ← mkFreshExprMVar (mkConst ``Oria.Grade) (userName := `g)
      let inferred := computation.toCarrier.toComputationType grade
      let body ← Term.withSynthesize <|
        if needsExit then elaborateBlock sequence inferred computation.toCarrier
        else Lean.Elab.Do.elabDoWith operations sequence (some inferred)
      let actual ← Program.Internal.computation? (← inferType body)
      let some actual := actual | return ← ensureHasType expectedType body
      let left ← normalizeGrade actual.grade
      let right ← normalizeGrade computation.grade
      unless ← isDefEq left.expr right.expr do
        match ← gradeDocument? left.expr, ← gradeDocument? right.expr with
        | some actual, some declared =>
          throwError "Oria `do` grade mismatch\ninferred: {actual}\ndeclared: {declared}"
        | _, _ => return ← ensureHasType expectedType body
      let same ← mkEqTrans (← left.getProof) (← mkEqSymm (← right.getProof))
      let family ← withLocalDeclD `g (mkConst ``Oria.Grade) fun g =>
        mkLambdaFVars #[g] (actual.toCarrier.toComputationType g)
      let proof ← mkCongrArg family same
      ensureHasType expectedType (← mkEqMP proof body)

@[term_elab «do»] public meta def elaborate : TermElab := fun stx expectedType? => do
  let `(do $sequence) := stx | throwUnsupportedSyntax
  let some expectedType := expectedType? | throwUnsupportedSyntax
  elaborateSequence sequence expectedType

end Oria.Elab.ProgDo
