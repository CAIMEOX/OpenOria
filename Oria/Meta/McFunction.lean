module

public import Oria.Language.Builder
public import Lean.Elab.Command
public import Lean.EnvExtension
public import Oria.Meta.Objects
public import Oria.IR.Tree.Dependencies
meta import all Oria.Meta.McFunction.Eval
meta import all Oria.Language.Builder
import Lean.Compiler.IR.EmitUtil
import Qq.MetaM

namespace Oria.McFunctionRegistry

open Lean

/-- Stable metadata persisted for one attributed object function. -/
public structure Entry where
  signature : Signature
  signatureName : Name
  refName : Name
  callName : Name
  elaborated : Option ElaboratedDef

private instance : Inhabited Entry where
  default :=
    { signature := { args := [], result := .unit, grade := .pure }
      signatureName := .anonymous
      refName := .anonymous
      callName := .anonymous
      elaborated := none }

private initialize declarations : MapDeclarationExtension Entry ←
  mkMapDeclarationExtension

public def find? (env : Environment) (decl : Name) : Option Entry :=
  declarations.find? env decl

private def insert (env : Environment) (decl : Name) (entry : Entry) : Environment :=
  declarations.insert env decl entry

public def elaborate
    (env : Environment) (decl : Name) :
    Except Diagnostic ElaboratedDef := do
  let some entry := find? env decl
    | throw (.unknownMcFunction decl)
  let some elaborated := entry.elaborated
    | throw (.invalidMcFunctionEntry decl)
  unless elaborated.source == decl && elaborated.signature == entry.signature do
    throw (.invalidMcFunctionEntry decl)
  pure elaborated

end Oria.McFunctionRegistry

namespace Oria.McFunction

open Lean Lean.Elab Lean.Elab.Command Lean.Meta
open Oria.IR
open Qq

private structure ValueParam where
  code : Q(ObjTy)
  value : Q(IR.Tree.Expr $code)

private structure Shape where
  signature : Q(Signature)
  callValue : Expr

private def valView (type : Expr) :
    MetaM ((A : Q(Type)) × (a : Q(ObjTy)) × Q(Object $A $a) × Q(Region)) := do
  let type ← withReducible <| whnf type
  let_expr Val source region code object := type
    | throwError "mcfunction parameters must have type `Val A`{indentExpr type}"
  pure ⟨source, code, object, region⟩

private def progView (type : Expr) :
    MetaM (Q(Grade) × (A : Q(Type)) × (a : Q(ObjTy)) × Q(Object $A $a) × Q(Region)) := do
  let type ← withReducible <| whnf type
  let_expr Prog grade source region code object := type
    | throwError "mcfunction result must have type `Prog grade A`{indentExpr type}"
  pure ⟨grade, source, code, object, region⟩

private def treeArgs (params : Array ValueParam) :
    (types : Q(List ObjTy)) × Q(Args IR.Tree.Expr $types) :=
  params.foldr (init := ⟨q([]), q(Args.nil)⟩) fun param ⟨types, args⟩ =>
    ⟨q($(param.code) :: $types), q(Args.cons $(param.value) $args)⟩

private def analyze (decl type : Expr) : MetaM Shape :=
  forallTelescopeReducing type fun values result => do
    let mut params := #[]
    for value in values do
      let localDecl ← value.fvarId!.getDecl
      if localDecl.binderInfo == .implicit && (← isDefEq localDecl.type q(Region)) then
        continue
      unless localDecl.binderInfo == .default do
        throwError "mcfunction parameters must be explicit"
      let ⟨source, code, object, region⟩ ← valView localDecl.type
      if source.hasFVar || code.hasFVar then
        throwError "mcfunction parameter types must be closed"
      have value : Q(@Val $source $region $code $object) := value
      params := params.push { code, value := q(Val.expr $value) }
    let ⟨grade, resultSource, resultCode, object, region⟩ ← progView result
    if grade.hasFVar || resultSource.hasFVar || resultCode.hasFVar then
      throwError "mcfunction result type and grade must not depend on parameters"
    let ⟨codes, args⟩ := treeArgs params
    let decl : Q(DeclRef ⟨$codes, $resultCode, $grade⟩) := decl
    let tree : Q(IR.Tree.Tree $grade $resultCode) := q(IR.Tree.Tree.perform (.call $decl $args))
    let call := q(@makeProg $grade $resultSource $region $resultCode $object (pure $tree))
    let callValue ← mkLambdaFVars values call
    pure { signature := q(⟨$codes, $resultCode, $grade⟩), callValue }

private def localIRClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some decl := Lean.IR.findEnvDecl env name then
        pending := (Lean.IR.collectUsedDecls env [decl]).toList ++ pending
  return seen

private def exposeIRForMeta (env : Environment) (root : Name) : Environment :=
  (localIRClosure env [root]).toList.foldl setDeclMeta env

private def addDefinition
    (name : Name) (type value : Expr)
    (hints : ReducibilityHints := .opaque) :
    CoreM Unit := do
  addAndCompile (.defnDecl {
    name
    levelParams := []
    type
    value
    hints
    safety := .safe
  }) (logCompileErrors := true)

private def generatedNames (decl : Name) : Name × Name × Name :=
  (decl ++ `signature, decl ++ `ref, decl ++ `call)

private def addMcFunction
    (decl : Name) (attr : Syntax) (kind : AttributeKind) : CoreM Unit := do
  Attribute.Builtin.ensureNoArgs attr
  unless kind == .global do
    throwErrorAt attr "`mcfunction` only supports a global attribute"
  let env ← getEnv
  if env.getModuleIdxFor? decl |>.isSome then
    throwErrorAt attr "`mcfunction` must be applied in the declaration's defining module"
  if McFunctionRegistry.find? env decl |>.isSome then
    throwErrorAt attr "declaration `{decl}` is already an mcfunction"
  let some asyncInfo := env.findAsync? decl
    | throwErrorAt attr "unknown declaration `{decl}`"
  let info := asyncInfo.toConstantVal
  unless info.levelParams.isEmpty do
    throwErrorAt attr "mcfunction declarations cannot be universe-polymorphic"
  if let .defnInfo definition := asyncInfo.toConstantInfo then
    if definition.value.hasSorry then return
    unless definition.safety == .safe do
      throwErrorAt attr "mcfunction declarations must be safe definitions"
  let (signatureName, refName, callName) := generatedNames decl
  for name in [signatureName, refName, callName] do
    if env.contains name then
      throwErrorAt attr "generated mcfunction declaration `{name}` already exists"
  let shape ← MetaM.run' <| analyze (mkConst refName) info.type
  let (_, staged) ← withoutModifyingEnv' do
    modifyEnv (exposeIRForMeta · decl)
    let recipeValue ← MetaM.run' do
      let u ← getDecLevel info.type
      have F : Q(Type $u) := info.type
      have sig : Q(Signature) := shape.signature
      have build : Q($F) := mkConst decl
      let builder ← synthInstanceQ q(BuildFn $F $sig)
      pure q(@McFunction.Internal.capture $F $sig $decl $build $builder)
    let elaborated ← MetaM.run' do
      let recipe ←
        match ← McFunction.Eval.recipe recipeValue with
        | .ok recipe => pure recipe
        | .error error => throwErrorAt attr "failed to evaluate mcfunction `{decl}`: {error}"
      pure (McFunction.Internal.Recipe.compile recipe)
    match ObjectRegistry.checkPersistent (← getEnv)
        elaborated.definition.dependencies.persistentTypes.toArray with
    | .ok () => pure ()
    | .error diagnostic => throwErrorAt attr "{repr diagnostic}"
    addDefinition signatureName q(Signature) shape.signature .abbrev
    let sig : Q(Signature) := mkConst signatureName
    addDefinition refName q(DeclRef $sig) q(⟨.named $decl⟩ : DeclRef $sig)
    let bodyName := mkPrivateName (← getEnv) (callName ++ `body)
    withoutExporting do
      addDefinition bodyName info.type shape.callValue
    addDefinition callName info.type (mkConst bodyName)
    modifyEnv (exposeIRForMeta · callName)
    setEnv <| McFunctionRegistry.insert (← getEnv) decl {
      signature := elaborated.signature
      signatureName
      refName
      callName
      elaborated := some elaborated
    }
  setEnv staged

initialize registerBuiltinAttribute {
  name := `mcfunction
  descr := "Reify a closed `Val ... → Prog ...` builder as an Oria object function."
  applicationTime := .afterCompilation
  add := addMcFunction
}

end Oria.McFunction
