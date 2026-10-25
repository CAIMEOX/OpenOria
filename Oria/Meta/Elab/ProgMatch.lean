module

public meta import Oria.Meta.Quote
public import Oria.Meta.Elab.ProgDo
public import Oria.Language.Object
public meta import Oria.Meta.ObjectDerive
public meta import Oria.Meta.Elab.Program.Internal
public meta import Lean.Elab.BuiltinDo.Match
meta import all Oria.Language.Builder
meta import all Oria.Meta.Elab.Program.Internal
public meta import Qq.MetaM

public section

namespace Oria.Elab.ProgMatch

open Lean Lean.Elab Lean.Elab.Term Lean.Meta
open Lean.Parser.Term
open Lean.Meta.Match
open Qq

private abbrev BinderId := Nat
private abbrev Carrier := Program.Internal.Carrier
private abbrev ConstructorView := Program.Internal.ConstructorView
private abbrev MatchFamily := Program.Internal.MatchFamily

/-- The source-pattern subset retained after Lean has resolved names and types. -/
private inductive Pattern where
  | wildcard (binder? : Option BinderId)
  | i32 (value : Int32)
  | constructor (family : MatchFamily) (name : Name) (fields : Array Pattern)

/-- One source-ordered matrix row. RHS syntax stays outside the pure compiler seam. -/
private structure MatrixRow where
  sourceIndex : Nat
  patterns : Array Pattern

/-- Information that must remain on the Lean-elaboration side of the matrix seam. -/
private structure BinderInfo where
  userName : Name
  sourceId : FVarId

private structure Discriminant where
  ref : Syntax
  expression : Expr
  carrier : Carrier

private structure ElaboratedRows where
  rows : Array MatrixRow
  binders : Array BinderInfo

private meta def inProgDo : Lean.Elab.Do.DoElabM Bool := do
  let computation ← Lean.Elab.Do.mkMonadApp (← read).doBlockResultType
  let computation := (← whnf computation).consumeMData
  return computation.isAppOfArity ``Oria.Prog 5

private meta def carrierForSource (source : Q(Type)) : TermElabM Carrier := do
  let code ← mkFreshExprMVarQ q(ObjTy) (userName := `a)
  let object ← synthInstanceQ q(Object $source $code)
  return { source, code := ← instantiateMVars code, object }

private meta def carrierForSourceExpr (source : Expr) : TermElabM Carrier := do
  have source : Q(Type) := source
  carrierForSource source

private meta partial def sourceOfTemplate
    (params : Array Expr) : TypeTemplate → TermElabM Expr
  | .param index => pure params[index]!
  | .nbt t => mkAppM ``Nbt.Data #[toExpr t]
  | .app name args => do
      let args ← args.attach.mapM fun arg => sourceOfTemplate params arg.val
      mkAppM name args.toArray

private meta def resolveFamily (carrier : Carrier) : TermElabM (Option MatchFamily) := do
  let source := (← whnf carrier.source).consumeMData
  let code := (← whnf carrier.code).consumeMData
  match_expr source with
  | _root_.Option element =>
    let_expr ObjTy.option code := code | return none
    let element : Q(Type) := element
    let code : Q(ObjTy) := code
    let object ← synthInstanceQ q(Object $element $code)
    let payload : Carrier := { source := element, code, object, region := carrier.region }
    return some {
      constructors := #[
        { name := ``_root_.Option.none, fields := #[],
          reference := mkApp (mkConst ``IR.Constructor.none) code },
        { name := ``_root_.Option.some, fields := #[payload],
          reference := mkApp (mkConst ``IR.Constructor.some) code }
      ]
    }
  | _ =>
    let .const sourceName _ := source.getAppFn | return none
    let some entry := Oria.ObjectRegistry.find? (← getEnv) sourceName | return none
    let sourceArgs := source.getAppArgs
    unless sourceArgs.size == entry.declaration.params do
      return none
    let_expr ObjTy.data owner := code | return none
    have owner : Q(TypeId) := owner
    let constructors ← entry.declaration.constructors.toArray.mapM fun constructor => do
      let fields ← constructor.fields.toArray.mapM fun field => do
        let fieldSource ← sourceOfTemplate sourceArgs field.type
        let field ← carrierForSourceExpr fieldSource
        pure { field with region := carrier.region }
      let fieldCodes := fields.foldr (init := q([])) fun field rest =>
        have code : Q(ObjTy) := field.code
        q($code :: $rest)
      have fieldCodes : Q(List ObjTy) := fieldCodes
      have constructorName : Q(Lean.Name) := toExpr constructor.name
      let reference : Expr := q(IR.Constructor.data
        (⟨$constructorName⟩ : IR.CtorRef $owner $fieldCodes))
      return { name := constructor.name, fields, reference }
    return some { constructors }

private meta def discriminant?
    (ref : Syntax) (expression : Expr) : TermElabM (Option Discriminant) := do
  let some carrier ← Program.Internal.carrier? (← inferType expression) | return none
  let source := (← whnf carrier.source).consumeMData
  let .const _ _ := source.getAppFn | return none
  return some { ref, expression, carrier }

private meta def Pattern.shiftBinders (offset : Nat) : Pattern → Pattern
  | .wildcard binder? => .wildcard (binder?.map (offset + ·))
  | .i32 value => .i32 value
  | .constructor family name fields =>
      .constructor family name (fields.map (Pattern.shiftBinders offset))

private meta def patternMatchType (sources : Array Expr) : MetaM Expr :=
  pure <| sources.foldr (init := mkConst ``Unit) fun source body =>
    mkForall `value .default source body

private meta def explicitBinder?
    (explicitNames : NameSet) (fvarId : FVarId) : MetaM (Option BinderInfo) := do
  let declaration ← fvarId.getDecl
  unless explicitNames.contains declaration.userName do
    return none
  return some {
    userName := declaration.userName
    sourceId := fvarId
  }

/-- Read the normalized host value through public integer conversions. Lean may expand
signed literals into constructor patterns; their internal representation stays in the front end. -/
private meta def integerPattern (ref : Syntax) (pattern : Lean.Meta.Match.Pattern) : TermElabM Pattern := do
  let value ← pattern.toExpr
  let bits ← mkAppM ``Int32.toUInt32 #[value]
  let nat ← mkAppM ``UInt32.toNat #[bits]
  let some n ← getNatValue? (← whnf nat)
    | throwErrorAt ref "an I32 pattern must be a constant integer or a variable"
  pure (.i32 (Int32.ofNat n))

mutual
  private meta def convertPattern
      (explicitNames : NameSet)
      (ref : Syntax)
      (carrier : Carrier) : Lean.Meta.Match.Pattern →
      StateRefT (Array BinderInfo) TermElabM Pattern
    | pattern@(.ctor name _ _ fields) => do
        if ← isDefEq carrier.code q(ObjTy.i32) then
          return ← integerPattern ref pattern
        match ← resolveFamily carrier with
        | none =>
            throwErrorAt ref "Oria `do` cannot inspect constructors of this object value"
        | some family =>
            let some constructor := family.constructors.find? (·.name == name)
              | throwErrorAt ref "internal object-match constructor is absent from its resolved family"
            let fields ← convertPatterns explicitNames ref fields constructor.fields.toList
            return .constructor family name fields.toArray
    | .var fvarId => do
        let binder? ← liftM <| explicitBinder? explicitNames fvarId
        match binder? with
        | none => return .wildcard none
        | some binder =>
            let binders ← get
            set (binders.push binder)
            return .wildcard (some binders.size)
    | .inaccessible _ =>
        throwErrorAt ref "Oria `do` object match does not support inaccessible patterns"
    | .as _ _ _ =>
        throwErrorAt ref "Oria `do` object match does not support `as` patterns"
    | pattern@(.val _) => do
        if ← isDefEq carrier.code q(ObjTy.i32) then
          return ← integerPattern ref pattern
        throwErrorAt ref "Oria `do` literal patterns require an I32 value"
    | .arrayLit _ _ =>
        throwErrorAt ref "Oria `do` object match does not support array patterns"

  private meta def convertPatterns
      (explicitNames : NameSet)
      (ref : Syntax) :
      List Lean.Meta.Match.Pattern → List Carrier →
      StateRefT (Array BinderInfo) TermElabM (List Pattern)
    | [], [] => pure []
    | pattern :: patterns, carrier :: carriers => do
        let pattern ← convertPattern explicitNames ref carrier pattern
        let patterns ← convertPatterns explicitNames ref patterns carriers
        return pattern :: patterns
    | _, _ =>
        throwErrorAt ref "internal object-match pattern telescope mismatch"
end

private meta def elaborateRow
    (discriminants : Array Discriminant)
    (sourceIndex : Nat)
    (alt : Term.MatchAltView ``doSeq) : TermElabM (MatrixRow × Array BinderInfo) := do
  let (patternVars, alt) ← Term.collectPatternVars alt
  let explicitNames := patternVars.foldl (init := {}) fun names patternVar =>
    names.insert patternVar.getId
  let matchType ← patternMatchType (discriminants.map (·.carrier.source))
  Term.withPatternVars patternVars fun patternVarDecls =>
    Lean.Elab.Do.withElaboratedLHS
      patternVarDecls
      alt.patterns
      alt.lhs
      discriminants.size
      matchType fun lhs => do
        let (patterns, binders) ←
          (convertPatterns explicitNames alt.lhs lhs.patterns
            (discriminants.map (·.carrier)).toList).run #[]
        return ({ sourceIndex, patterns := patterns.toArray }, binders)

private meta def elaborateRows
    (discriminants : Array Discriminant)
    (alts : Array (Term.MatchAltView ``doSeq)) :
    Lean.Elab.Do.DoElabM ElaboratedRows := do
  let mut rows := #[]
  let mut binders := #[]
  for h : index in *...alts.size do
    let (row, localBinders) ← liftM <| elaborateRow discriminants index alts[index]
    let offset := binders.size
    rows := rows.push {
      row with patterns := row.patterns.map (Pattern.shiftBinders offset)
    }
    binders := binders ++ localBinders
  return { rows, binders }

private meta def valueType (source : Name) : TermElabM Expr := do
  have source : Q(Type) := mkConst source
  let code ← mkFreshExprMVarQ q(ObjTy) (userName := `a)
  let object : Q(Object $source $code) ← mkInstMVar q(Object $source $code)
  return q(@Val $source Region.any $code $object)

private meta def isValueType (type : Expr) : MetaM Bool := do
  let type := (← withReducible <| whnf type).consumeMData
  return type.isAppOfArity ``Oria.Val 4

private meta def withRowBinders
    (binders : List (BinderId × Carrier))
    (infos : Array BinderInfo)
    (values : Array Expr)
    (next : Array Expr → Lean.Elab.Do.DoElabM Expr) : Lean.Elab.Do.DoElabM Expr :=
  match binders with
  | [] => next values
  | (id, carrier) :: rest => do
      let some info := infos[id]? | throwError "object-match binder is out of scope"
      withLocalDecl info.userName .default carrier.toType fun value => do
        pushInfoLeaf <| .ofFVarAliasInfo {
          id := value.fvarId!, baseId := info.sourceId, userName := info.userName }
        withRowBinders rest infos (values.push value) next

mutual
  private meta def patternExpr (carrier : Carrier) :
      Pattern → TermElabM (Expr × Array (BinderId × Carrier))
    | .wildcard none =>
        pure (mkApp (mkConst ``IR.Tree.Pattern.any) carrier.code, #[])
    | .wildcard (some id) =>
        pure (mkApp (mkConst ``IR.Tree.Pattern.bind) carrier.code, #[(id, carrier)])
    | .i32 value => pure (mkApp (mkConst ``IR.Tree.Pattern.i32) (toExpr value), #[])
    | .constructor family name fields => do
        let some constructor := family.constructors.find? (·.name == name)
          | throwError "object-match constructor is outside its family"
        let (fields, binders) ← patternsExpr constructor.fields.toList fields.toList
        let pattern ← mkAppM ``IR.Tree.Pattern.ctor #[constructor.reference, fields]
        pure (pattern, binders)

  private meta def patternsExpr :
      List Carrier → List Pattern → TermElabM (Expr × Array (BinderId × Carrier))
    | [], [] => pure (mkConst ``IR.Tree.Patterns.nil, #[])
    | carrier :: carriers, pattern :: patterns => do
        let (pattern, binders) ← patternExpr carrier pattern
        let (patterns, rest) ← patternsExpr carriers patterns
        let patterns ← mkAppM ``IR.Tree.Patterns.cons #[pattern, patterns]
        pure (patterns, binders ++ rest)
    | _, _ => throwError "object-match pattern telescope mismatch"
end

private meta def emitRows
    (discriminants : Array Discriminant)
    (alts : Array (Term.MatchAltView ``doSeq))
    (rows : ElaboratedRows)
    (resultType : Expr) : Lean.Elab.Do.DoElabM Expr := do
  let mut inputs : (types : Q(List ObjTy)) × Q(Args IR.Tree.Expr $types) :=
    ⟨q([]), q(Args.nil)⟩
  for discriminant in discriminants.reverse do
    let ⟨source, code, object, region⟩ := discriminant.carrier
    have value : Q(@Val $source $region $code $object) := discriminant.expression
    let expression : Q(IR.Tree.Expr $code) := q(Val.expr $value)
    let ⟨types, values⟩ := inputs
    inputs := ⟨q($code :: $types), q(Args.cons $expression $values)⟩
  let ⟨types, values⟩ := inputs
  let some computation ← Program.Internal.computation? (← Lean.Elab.Do.mkMonadApp resultType)
    | throwError "object match requires an Oria computation"
  let ⟨resultSource, resultCode, resultObject, resultRegion⟩ := computation.toCarrier
  let mut headGrade : Option Expr := none
  let mut tailGrades : Q(List Grade) := q([])
  let mut output : Expr := q((IR.Tree.Build.noRows :
    IR.Tree.Build (IR.Tree.Rows $types $resultCode [])))
  for row in rows.rows.reverse do
    let (patterns, binders) ← patternsExpr
      (discriminants.map (·.carrier)).toList row.patterns.toList
    let some alt := alts[row.sourceIndex]? | throwError "object-match row is out of bounds"
    let handler ← withRowBinders binders.toList rows.binders #[] fun parameters => do
      let continuation ← Lean.Elab.Do.DoElemCont.mkPure resultType
      let body ← Lean.Elab.Do.withDoBlockResultType resultType <|
        Lean.Elab.Do.elabDoSeq alt.rhs continuation
      mkLambdaFVars parameters body
    let handlerType ← inferType handler
    let bindingCodes := binders.foldr (init := q([])) fun (_, carrier) rest =>
      have code : Q(ObjTy) := carrier.code
      q($code :: $rest)
    let grade ← mkFreshExprMVarQ q(Grade)
    have handlerTypeQ : Q(Type) := handlerType
    have bindingCodesQ : Q(List ObjTy) := bindingCodes
    let builder ← synthInstanceQ
      q(BuildFn $handlerTypeQ ⟨$bindingCodesQ, $resultCode, $grade⟩)
    let lower ← mkAppM ``BuildFn.lower #[builder]
    let lowerHandler ← mkAppM' lower #[handler]
    let rowBuild ← mkAppM ``IR.Tree.Build.row #[patterns, lowerHandler]
    match headGrade with
    | none =>
        have emptyRows : Q(IR.Tree.Build (IR.Tree.Rows $types $resultCode [])) :=
          q(IR.Tree.Build.noRows)
        output ← mkAppM ``IR.Tree.Build.consRow #[rowBuild, emptyRows]
        headGrade := some grade
    | some head =>
        have headQ : Q(Grade) := head
        have oldGrades : Q(List Grade) := q($headQ :: $tailGrades)
        have oldRows : Q(IR.Tree.Build (IR.Tree.Rows $types $resultCode $oldGrades)) := output
        output ← mkAppM ``IR.Tree.Build.consRow #[rowBuild, oldRows]
        tailGrades := q($headQ :: $tailGrades)
        headGrade := some grade
  let some head := headGrade | throwError "object match has no rows"
  have headQ : Q(Grade) := head
  let gradesQ : Q(List Grade) := q($headQ :: $tailGrades)
  have valuesQ : Q(Args IR.Tree.Expr $types) := values
  have rowsQ : Q(IR.Tree.Build (IR.Tree.Rows $types $resultCode $gradesQ)) := output
  let build : Expr := q(Functor.map
    (fun rows => IR.Tree.Tree.matchMany $valuesQ rows) $(rowsQ))
  have gradeQ : Q(Grade) := q(Grade.joins $gradesQ)
  have buildQ : Q(IR.Tree.Build (IR.Tree.Tree $gradeQ $resultCode)) := build
  pure <| q(@makeProg $gradeQ $resultSource $resultRegion $resultCode $resultObject $buildQ)

private meta def elaborateObjectMatch
    (discriminants : Array Discriminant)
    (alts : Array (Term.MatchAltView ``doSeq))
    (dec : Lean.Elab.Do.DoElemCont) : Lean.Elab.Do.DoElabM Expr := do
  let isTail ← isValueType dec.resultType
  let branchResultType ← if isTail then
    pure dec.resultType
  else do
    let expectedUnit ← Lean.Elab.Do.mkPUnit
    unless ← isDefEq dec.resultType expectedUnit do
      throwError "object `match` appears in an unsupported dependent continuation"
    valueType ``Unit
  let alts ← liftMacroM <| Term.expandMacrosInPatterns alts
  let rows ← elaborateRows discriminants alts
  let result ← emitRows discriminants alts rows branchResultType
  if isTail then
    dec.mkBindUnlessPure result
  else
    let next ← dec.continueWithUnit
    withLocalDecl `ignored .default branchResultType fun ignored => do
      let continuation ← mkLambdaFVars #[ignored] next
      Lean.Elab.Do.mkBindApp
        branchResultType
        (← read).doBlockResultType
        result
        continuation

@[doElem_elab Lean.Parser.Term.doMatch]
public meta def elaborate : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doMatch| match $[(dependent := $dep)]? $[(generalizing := $gen?)]?
      $(motive?)? $discrs:matchDiscr,* with $alts:matchAlt*) := stx
    | throwUnsupportedSyntax
  let mut elaborated := #[]
  let mut hostCount := 0
  let mut hasNamedDiscriminant := false
  for discriminantSyntax in discrs.getElems do
    let `(matchDiscr| $[$h? :]? $term) := discriminantSyntax
      | throwUnsupportedSyntax
    if h?.isSome then
      hasNamedDiscriminant := true
    let expression ← Term.elabTerm term none
    match ← discriminant? term expression with
    | some discriminant =>
        elaborated := elaborated.push discriminant
    | none =>
        hostCount := hostCount + 1
  if elaborated.isEmpty then
    throwUnsupportedSyntax
  unless hostCount == 0 do
    throwErrorAt stx "Oria `do` cannot mix host and object match discriminants"
  if hasNamedDiscriminant then
    throwErrorAt stx "Oria `do` object match does not support named discriminants"
  if dep.isSome then
    throwErrorAt stx "Oria `do` object match does not support dependent matching"
  if gen?.isSome then
    throwErrorAt stx "Oria `do` object match does not support generalizing"
  if motive?.isSome then
    throwErrorAt stx "Oria `do` object match does not support a custom motive"
  elaborateObjectMatch elaborated (alts.filterMap (Term.getMatchAlt ``doSeq)) dec

private meta def patternContinuation (pattern : Term) (value : Ident)
    (otherwise? body? : Option (TSyntax ``doSeqIndent)) (dec : Lean.Elab.Do.DoElemCont) :
    Lean.Elab.Do.DoElabM Expr := do
  let success := match body? with
    | none => dec.continueWithUnit
    | some body => Lean.Elab.Do.elabDoSeq ⟨body.raw⟩ dec
  Lean.Elab.Do.doElabToSyntax "pattern binding continuation" success fun rest => do
    let rest ← `(doSeq| $rest:term)
    let statement ← match otherwise? with
      | none => `(doElem| match $value:ident with | $pattern:term => $rest)
      | some otherwise =>
        `(doElem| match $value:ident with | $pattern:term => $rest | _ => $otherwise:doSeqIndent)
    let continuation ← Lean.Elab.Do.DoElemCont.mkPure (← read).doBlockResultType
    Lean.Elab.Do.elabDoElem statement continuation

/-- Pattern bindings use the selected object carrier and the ordinary pattern matrix compiler. -/
@[doElem_elab Lean.Parser.Term.doLetArrow]
public meta def elaboratePatternBind : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doLetArrow| let%$ref $[mut%$_]? $config:letConfig $decl) := stx | throwUnsupportedSyntax
  let `(doPatDecl| $pattern $[: $type]? ← $action $[| $otherwise $[$body]?]?) := decl
    | throwUnsupportedSyntax
  if pattern.raw.isIdent || (pattern.raw.isOfKind ``Lean.Parser.Term.hole && otherwise.isNone) then
    throwUnsupportedSyntax
  let name ← mkFreshUserName `patternValue
  let value := mkIdentFrom ref name
  let binding ← `(doElem| let $config:letConfig $value:ident $[: $type]? ← $action)
  let next : Lean.Elab.Do.DoElemCont := {
    resultName := ← mkFreshUserName `patternBound
    resultType := ← Lean.Elab.Do.mkPUnit
    k := patternContinuation pattern value otherwise body.join dec
  }
  ProgDo.elaborateLetArrow binding next

/-- Object let-patterns elaborate through the same source-typed match as arrow bindings. -/
@[doElem_elab Lean.Parser.Term.doLet]
public meta def elaboratePurePattern : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doLet| let%$ref $[mut]? $config:letConfig $decl:letDecl) := stx
    | throwUnsupportedSyntax
  let `(letDecl| $pattern:term $[: $type]? := $rhs) := decl | throwUnsupportedSyntax
  let saved ← saveState
  let expected ← type.mapM (fun type => Term.elabType type)
  let value ← Term.elabTerm rhs expected
  unless (← Program.Internal.carrier? (← inferType value)).isSome do
    saved.restore
    throwUnsupportedSyntax
  saved.restore
  let value := mkIdentFrom ref (← mkFreshUserName `patternValue)
  let binding ← `(doElem| let $config:letConfig $value:ident $[: $type]? := $rhs)
  let next : Lean.Elab.Do.DoElemCont := {
    resultName := ← mkFreshUserName `patternBound
    resultType := ← Lean.Elab.Do.mkPUnit
    k := patternContinuation pattern value none none dec
  }
  ProgDo.elaborateLet binding next

/-- A fallback pattern branch uses the enclosing object's return continuation. -/
@[doElem_elab Lean.Parser.Term.doLetElse]
public meta def elaboratePatternLet : Lean.Elab.Do.DoElab := fun stx dec => do
  unless ← inProgDo do throwUnsupportedSyntax
  let `(doLetElse| let%$ref $[mut]? $config:letConfig $pattern := $rhs | $otherwise $[$body]?) := stx
    | throwUnsupportedSyntax
  let name ← mkFreshUserName `patternValue
  let value := mkIdentFrom ref name
  let binding ← `(doElem| let $config:letConfig $value:ident := $rhs)
  let next : Lean.Elab.Do.DoElemCont := {
    resultName := ← mkFreshUserName `patternBound
    resultType := ← Lean.Elab.Do.mkPUnit
    k := patternContinuation pattern value (some otherwise) body dec
  }
  Lean.Elab.Do.elabDoElem binding next

end Oria.Elab.ProgMatch
