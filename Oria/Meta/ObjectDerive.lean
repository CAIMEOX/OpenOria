module

public import Oria.Language.Object
public import Oria.IR.Common.Schema
public import Lean.Elab.Deriving.Basic
public import Lean.Elab.Deriving.Util
public import Lean.EnvExtension
import Oria.Meta.Quote
import Qq.Macro
import Qq.Typ
meta import all Oria.Language.Builder
meta import all Oria.Language.Object.Type
namespace Oria.ObjectRegistry

open Lean

/-- The canonical declaration and generated source names for one registered datatype. -/
public structure ObjectEntry where
  declaration : ObjectDecl
  idName : Name
  codeName : Name
  objectName : Name
  schemaName : Name
  builders : List (Name × Name) := []
  projections : List (Name × Name) := []
  deriving Repr

private instance : Inhabited ObjectEntry where
  default :=
    { declaration := { name := .anonymous, params := 0, constructors := [] }
      idName := .anonymous
      codeName := .anonymous
      objectName := .anonymous
      schemaName := .anonymous }

private initialize declarations : MapDeclarationExtension ObjectEntry ←
  mkMapDeclarationExtension

/-- Look up a derived object across the current module or imported `.olean` files. -/
public def find? (env : Environment) (typeName : Name) : Option ObjectEntry :=
  declarations.find? env typeName

/-- Resolve a source constructor to the typed builder registered by its derivation. -/
public def builder? (env : Environment) (name : Name) : Option Name := do
  let .ctorInfo ctor ← env.find? name | none
  let entry ← find? env ctor.induct
  entry.builders.lookup name

/-- Resolve a host structure projection to its region-preserving object projection. -/
public def projection? (env : Environment) (name : Name) : Option Name := do
  let info ← env.getProjectionFnInfo? name
  let .ctorInfo constructor ← env.find? info.ctorName | none
  let entry ← find? env constructor.induct
  entry.projections.lookup name

private def insert
    (env : Environment) (typeName : Name) (entry : ObjectEntry) : Environment :=
  declarations.insert env typeName entry

end Oria.ObjectRegistry

namespace Oria.ObjectDerive

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Meta
open Lean.Parser Lean.Parser.Term
open Qq

initialize valueTypeAttribute : TagAttribute ←
  registerTagAttribute `value_type
    "Represent a closed, pointer-free, single-constructor object by its field words."
    (validate := fun name => do
    let .inductInfo info ← getConstInfo name
      | throwError "`value_type` requires an inductive or structure declaration"
    unless info.ctors.length == 1 do
      throwError "`value_type` requires exactly one constructor"
    if (ObjectRegistry.find? (← getEnv) name).isSome then
      throwError "set `value_type` before deriving Oria.Object")

private inductive Primitive where
  | unit
  | bool
  | i32

private def Primitive.template : Primitive → TypeTemplate
  | .unit => .app ``Unit []
  | .bool => .app ``Bool []
  | .i32 => .app ``Int32 []

private structure Parameter where
  name : Name
  type : Expr

private structure Field where
  label : Name
  source : TypeTemplate

private structure Constructor where
  name : Name
  fields : Array Field

private structure Summary where
  typeName : Name
  params : Array Parameter
  constructors : Array Constructor
  repr : ReprHint

private structure Names where
  typeName : Name
  id : Name
  code : Name
  object : Name
  schema : Name

private def generatedNames (typeName : Name) : Names :=
  let ns := typeName.append `Oria
  { typeName
    id := ns.append `id
    code := ns.append `code
    object := ns.append `object
    schema := ns.append `schema }

private def rootedIdent (name : Name) : Ident :=
  mkIdent (rootNamespace ++ name)

private def builderNamespace (typeName : Name) : Name :=
  typeName.append `Obj

private def constructorNamespace (typeName : Name) : Name :=
  (builderNamespace typeName).append `Ctor

private def baseName (name : Name) : String :=
  name.eraseMacroScopes.getString!

private def constructorBuilderName (typeName constructorName : Name) : Name :=
  Name.str (constructorNamespace typeName) (baseName constructorName)

private def projectionName (typeName field : Name) : Name :=
  typeName.append `Obj |>.append `Field |>.append field

private def primitive? (type : Expr) : Option Primitive :=
  if type.isConstOf ``Unit || type.isConstOf ``PUnit then some .unit
  else if type.isConstOf ``Bool then some .bool
  else if type.isConstOf ``Int32 then some .i32
  else none

private def fieldName (decl : LocalDecl) (index : Nat) : Name :=
  let name := decl.userName.eraseMacroScopes
  if name.isAnonymous then Name.mkSimple s!"field{index}" else name

private def unsupportedField {α : Type} (type : Expr) : TermElabM α :=
  throwError "Oria.Object field type must be a closed first-order named type{indentExpr type}"

private def dependentField {α : Type} (type : Expr) : TermElabM α :=
  throwError "Oria.Object does not support dependent proof/runtime-dependent fields{indentExpr type}"

private def checkRegular
    (typeName : Name) (params : Array Parameter) (args : List TypeTemplate) : TermElabM Unit := do
  let expected := (List.range params.size).map TypeTemplate.param
  unless args == expected do
    throwError "Oria.Object rejects non-regular recursion for {.ofConstName typeName}"

private partial def templateOf
    (env : Environment)
    (typeName : Name)
    (groupNames : NameSet)
    (paramFVars : Array FVarId)
    (paramInfo : Array Parameter)
    (type : Expr) : TermElabM TypeTemplate := do
  let type ← whnf (← instantiateMVars type)
  if let .fvar fvar := type then
    if let some index := paramFVars.findIdx? (· == fvar) then
      return .param index
    else
      dependentField type
  if let some primitive := primitive? type then
    return primitive.template
  if type.isAppOfArity ``Nbt.Data 1 then
    let tag ← whnf type.getAppArgs[0]!
    if tag.isAppOfArity ``_root_.Option.none 1 then return .nbt none
    if tag.isAppOfArity ``_root_.Option.some 2 then
      let value ← whnf tag.getAppArgs[1]!
      for t in ([.byte, .short, .int, .long, .float, .double, .string,
          .byteArray, .intArray, .longArray, .list, .compound] : List Nbt.Tag) do
        if ← isDefEq value (toExpr t) then return .nbt (some t)
    unsupportedField type
  if type.isAppOfArity ``Option 1 then
    let element := type.getAppArgs[0]!
    return .app ``Option [← templateOf env typeName groupNames paramFVars paramInfo element]
  if type.isAppOfArity ``Persistent.Ref 1 then
    let element := type.getAppArgs[0]!
    return .app ``Persistent.Ref [← templateOf env typeName groupNames paramFVars paramInfo element]
  let .const sourceName _ := type.getAppFn
    | unsupportedField type
  let arguments ←
    type.getAppArgs.toList.mapM (templateOf env typeName groupNames paramFVars paramInfo)
  if sourceName == typeName || groupNames.contains sourceName then
    checkRegular typeName paramInfo arguments
  else if (ObjectRegistry.find? env sourceName).isNone then
    throwError "Oria.Object field type is not a registered Oria object{indentExpr type}"
  return .app sourceName arguments

private def inspectConstructor
    (env : Environment)
    (typeName : Name)
    (groupNames : NameSet)
    (ind : InductiveVal)
    (params : Array Parameter)
    (name : Name) : TermElabM Constructor := do
  let constructor ← getConstInfoCtor name
  unless constructor.numParams = ind.numParams do
    throwError "inconsistent parameter count for {.ofConstName name}"
  forallTelescopeReducing constructor.type fun arguments _ => do
    unless arguments.size = constructor.numParams + constructor.numFields do
      throwError "unexpected constructor telescope for {.ofConstName name}"
    let mut fields := #[]
    let mut paramFVars := #[]
    for index in *...constructor.numParams do
      paramFVars := paramFVars.push arguments[index]!.fvarId!
    for index in *...constructor.numFields do
      let parameter := arguments[constructor.numParams + index]!
      let localDecl ← parameter.fvarId!.getDecl
      let fieldType ← inferType parameter
      let fieldType ← instantiateMVars fieldType
      if ind.numNested != 0 then
        let recursive := (fieldType.find? fun expression =>
          match expression with
          | .const name _ => groupNames.contains name
          | _ => false).isSome
        let head := fieldType.getAppFn
        let direct := match head with
          | .const name _ => groupNames.contains name
          | _ => false
        unless !recursive || direct || head.isConstOf ``Persistent.Ref do
          throwError "Oria.Object supports nested recursion through persistent Ref fields"
      let fieldSort ← whnf (← inferType fieldType)
      if fieldSort.isProp then
        dependentField fieldType
      let template ← templateOf env typeName groupNames paramFVars params fieldType
      fields := fields.push { label := fieldName localDecl index, source := template }
    return { name, fields }

private def validate
    (typeName : Name) (ind : InductiveVal) : CommandElabM (Array Parameter) := do
  if isPrivateName typeName then
    throwError "Oria.Object does not support private inductives"
  if typeName == ``Persistent.Ref then
    throwError "persistent Ref has a built-in object representation"
  unless ind.levelParams.isEmpty do
    throwError "Oria.Object does not support universe-polymorphic types"
  unless ind.numIndices = 0 do
    throwError "Oria.Object does not support indexed inductives"
  if ind.isUnsafe then
    throwError "Oria.Object rejects inductives outside Lean's safe fragment"
  if ind.ctors.isEmpty then
    throwError "Oria.Object does not support empty inductives"
  if ind.ctors.any isPrivateName then
    throwError "Oria.Object does not support private constructors"
  let params ← liftTermElabM <| forallTelescopeReducing ind.type fun telescope result => do
      let mut params := #[]
      unless result == .sort (.succ .zero) do
        throwError "Oria.Object source types must inhabit Type"
      unless telescope.size == ind.numParams do
        throwError "Oria.Object found an inconsistent parameter telescope"
      for parameter in telescope do
        let localDecl ← parameter.fvarId!.getDecl
        let parameterType ← whnf (← inferType parameter)
        unless parameterType == .sort (.succ .zero) do
          throwError "Oria.Object parameters must be ordinary Type-level parameters"
        params := params.push { name := localDecl.userName.eraseMacroScopes, type := parameterType }
      return params
  return params

private partial def templateCodeTerm
    (codes : Array Ident) : TypeTemplate → TermElabM Term
  | .param index => pure codes[index]!
  | .nbt tag => pure (Syntax.mkCApp ``ObjTy.nbt #[quoteNbtTag tag])
  | .app name args => do
      let args ← args.toArray.mapM (templateCodeTerm codes)
      if name == ``Unit && args.isEmpty then
        pure (mkCIdent ``ObjTy.unit)
      else if name == ``Bool && args.isEmpty then
        pure (mkCIdent ``ObjTy.bool)
      else if name == ``Int32 && args.isEmpty then
        pure (mkCIdent ``ObjTy.i32)
      else if name == ``Option && args.size == 1 then
        pure (Syntax.mkCApp ``ObjTy.option args)
      else if name == ``Persistent.Ref && args.size == 1 then
        pure (Syntax.mkCApp ``ObjTy.ref args)
      else
        let id ← `({ name := $(quote name), args := [$args,*] })
        pure (Syntax.mkCApp ``ObjTy.data #[id])

private def parameterBinders
    (params : Array Parameter) (sourceIds codeIds : Array Ident) :
    TermElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinderF)) := do
  let mut binders := #[]
  for index in *...params.size do
    binders := binders.push (←
      `(bracketedBinderF| {$(sourceIds[index]!):ident : Type}))
    binders := binders.push (←
      `(bracketedBinderF| {$(codeIds[index]!):ident : Oria.ObjTy}))
    binders := binders.push (←
      `(bracketedBinderF| [Oria.Object $(sourceIds[index]!):ident $(codeIds[index]!):ident]))
  return binders

private def objectCommands
    (summary : Summary) : TermElabM (Array Command) := do
  let names := generatedNames summary.typeName
  let mut sourceIds := #[]
  let mut codeIds := #[]
  for parameter in summary.params do
    sourceIds := sourceIds.push (mkIdent parameter.name)
    codeIds := codeIds.push (mkIdent (parameter.name.appendAfter "_code"))
  let binders ← parameterBinders summary.params sourceIds codeIds
  let codeTerms : Array Term := codeIds.map (fun id => id)
  let ownerId ← `({ name := $(quote summary.typeName), args := [$codeTerms,*] })
  let ownerCode := Syntax.mkCApp ``ObjTy.data #[ownerId]
  let idCommand ← `(
    public abbrev $(rootedIdent names.id):ident $binders:bracketedBinder* : Oria.TypeId :=
      $ownerId:term)
  let codeCommand ← `(
    public abbrev $(rootedIdent names.code):ident $binders:bracketedBinder* : Oria.ObjTy :=
      $ownerCode:term)
  let schemaConstructors ← summary.constructors.mapM fun constructor => do
    let fields ← constructor.fields.mapM fun field => templateCodeTerm codeIds field.source
    `({ name := $(quote constructor.name)
        fields := [$fields,*] })
  let repr := mkCIdent (match summary.repr with
    | .ordinary => ``ReprHint.ordinary | .value => ``ReprHint.value)
  let schemaCommand ← `(
    public def $(rootedIdent names.schema):ident $binders:bracketedBinder* : Oria.ObjectSchema :=
      { id := $ownerId:term, constructors := [$schemaConstructors,*], repr := $repr })
  return #[idCommand, codeCommand, schemaCommand]

private partial def sourceTemplateExpr
    (params : Array Expr) : TypeTemplate → TermElabM Expr
  | .param index => pure params[index]!
  | .nbt tag => mkAppM ``Nbt.Data #[toExpr tag]
  | .app name args => do
      let args ← args.attach.mapM fun arg => sourceTemplateExpr params arg.val
      mkAppM name args.toArray

private def listExpr (values : Array Expr) : Expr :=
  let alpha := Lean.mkConst ``ObjTy
  values.foldr (init := mkApp (mkConst ``List.nil [Level.zero]) alpha) fun value rest =>
    mkAppN (mkConst ``List.cons [Level.zero]) #[alpha, value, rest]

private def codeTemplateExpr
    (codes : Array Expr) : TypeTemplate → Expr
  | .param index => codes[index]!
  | .nbt tag => mkApp (mkConst ``ObjTy.nbt) (toExpr tag)
  | .app name args =>
      let values := args.attach.map (fun arg => codeTemplateExpr codes arg.val) |>.toArray
      if name == ``Unit && values.isEmpty then
        mkConst ``ObjTy.unit
      else if name == ``Bool && values.isEmpty then
        mkConst ``ObjTy.bool
      else if name == ``Int32 && values.isEmpty then
        mkConst ``ObjTy.i32
      else if name == ``Option && values.size == 1 then
        mkApp (mkConst ``ObjTy.option) values[0]!
      else if name == ``Persistent.Ref && values.size == 1 then
        mkApp (mkConst ``ObjTy.ref) values[0]!
      else
        let id := mkApp2 (mkConst ``TypeId.mk) (toExpr name) (listExpr values)
        mkApp (mkConst ``ObjTy.data) id
termination_by template => sizeOf template
decreasing_by
  simp_wf
  have smaller := List.sizeOf_lt_of_mem arg.property
  omega

private partial def withObjectParams
    {α : Type}
    (params : List Parameter)
    (next : Array Expr → Array Expr → Array Expr → Array Expr → TermElabM α) :
    TermElabM α :=
  go params #[] #[] #[] #[]
where
  go
      (params : List Parameter)
      (sources codes instances all : Array Expr) : TermElabM α := do
    match params with
    | [] => next sources codes instances all
    | parameter :: rest =>
      withLocalDecl parameter.name .implicit parameter.type fun source =>
        withLocalDecl (parameter.name.appendAfter "_code") .implicit
            (mkConst ``ObjTy) fun code =>
          let objectType := mkApp2 (mkConst ``Object) source code
          withLocalDecl (parameter.name.appendAfter "_object") .instImplicit objectType fun object =>
            go rest (sources.push source) (codes.push code) (instances.push object)
              (all.push source |>.push code |>.push object)

private def objectTypeExpr
    (source : Expr) (code : Expr) : Expr :=
  mkApp2 (mkConst ``Object) source code

private def addObjectInstance (summary : Summary) : CommandElabM Unit := do
  let names := generatedNames summary.typeName
  let (type, value) ← liftTermElabM <|
    withObjectParams summary.params.toList fun sources codes _ allParams => do
      let source := mkAppN (mkConst summary.typeName) sources
      let owner := mkApp2 (mkConst ``TypeId.mk) (toExpr summary.typeName) (listExpr codes)
      let code := mkApp (mkConst ``ObjTy.data) owner
      let objectType := objectTypeExpr source code
      let type ← mkForallFVars allParams objectType
      let value : Expr := mkAppN (mkConst ``makeObject) #[source, code]
      let value ← mkLambdaFVars allParams value
      pure (type, value)
  liftCoreM <| withExporting do
    addAndCompile (.defnDecl {
      name := names.object
      levelParams := []
      type
      value
      hints := .regular 1
      safety := .safe
    }) (logCompileErrors := true)
  liftTermElabM <| registerInstance names.object .global (eval_prio default)

private def addConstructor
    (summary : Summary) (constructor : Constructor) : CommandElabM Unit := do
  let name := constructorBuilderName summary.typeName constructor.name
  let (type, value) ← liftTermElabM <|
    withObjectParams summary.params.toList fun sources codes _ allParams => do
      let source := mkAppN (mkConst summary.typeName) sources
      let owner := mkApp2 (mkConst ``TypeId.mk) (toExpr summary.typeName) (listExpr codes)
      let code := mkApp (mkConst ``ObjTy.data) owner
      let object ← synthInstance (objectTypeExpr source code)
      let rec addFields
          (fields : List Field)
          (values codes' all : Array Expr)
          (k : Array Expr → Array Expr → Array Expr → TermElabM (Expr × Expr)) :
          TermElabM (Expr × Expr) := do
        match fields with
        | [] => k values codes' all
        | field :: rest =>
          let fieldSource ← sourceTemplateExpr sources field.source
          let fieldCode := codeTemplateExpr codes field.source
          let fieldObject ← synthInstance (objectTypeExpr fieldSource fieldCode)
          let fieldType := mkAppN (mkConst ``Val)
            #[fieldSource, mkConst ``Region.any, fieldCode, fieldObject]
          withLocalDecl field.label .default fieldType fun value =>
            addFields rest (values.push value) (codes'.push fieldCode) (all.push value) k
      addFields constructor.fields.toList #[] #[] allParams fun values fieldCodes all => do
        let fieldCodesExpr := listExpr fieldCodes
        let mut args := Lean.mkAppN (Lean.mkConst ``Args.nil [Level.zero, Level.zero])
          #[Lean.mkConst ``ObjTy, Lean.mkConst ``IR.Tree.Expr]
        for index in (List.range values.size).reverse do
          let valueExpr ← mkAppM ``Val.expr #[values[index]!]
          args ← mkAppM ``Args.cons #[valueExpr, args]
        have ownerQ : Q(TypeId) := owner
        have fieldCodesQ : Q(List ObjTy) := fieldCodesExpr
        have nameQ : Q(Lean.Name) := toExpr constructor.name
        have ctorRefQ : Q(IR.CtorRef $ownerQ $fieldCodesQ) :=
          q((⟨$nameQ⟩ : IR.CtorRef $ownerQ $fieldCodesQ))
        have ctorQ : Q(IR.Constructor (.data $ownerQ) $fieldCodesQ) :=
          q(IR.Constructor.data $ctorRefQ)
        let expectedArgs := mkApp2 (mkConst ``Args)
          (mkConst ``IR.Tree.Expr) fieldCodesExpr
        let _ ← isDefEq (← inferType args) expectedArgs
        let primitive ← mkAppM ``IR.Tree.Prim.construct #[ctorQ, args]
        let tree ← mkAppM ``IR.Tree.Tree.perform #[primitive]
        have codeQ : Q(ObjTy) := code
        have treeQ : Q(IR.Tree.Tree .pure $codeQ) := tree
        let build : Expr :=
          q((pure $treeQ : IR.Tree.Build (IR.Tree.Tree .pure $codeQ)))
        let body := mkAppN (mkConst ``makeProg)
          #[mkConst ``Grade.pure, source, mkConst ``Region.any, code, object, build]
        let resultType := mkAppN (mkConst ``Prog)
          #[mkConst ``Grade.pure, source, mkConst ``Region.any, code, object]
        let all := all
        let type ← mkForallFVars all resultType
        let value ← mkLambdaFVars all body
        pure (type, value)
  liftCoreM <| withExporting do
    addAndCompile (.defnDecl {
      name
      levelParams := []
      type
      value
      hints := .regular 1
      safety := .safe
    }) (logCompileErrors := true)

private def addProjections (summary : Summary) : CommandElabM Unit := do
  let some info := getStructureInfo? (← getEnv) summary.typeName | return
  let some constructor := summary.constructors[0]? | return
  for i in [:info.fieldNames.size] do
    let fieldName := info.fieldNames[i]!
    let some field := constructor.fields[i]? | throwError "record field metadata does not match its constructor"
    let name := projectionName summary.typeName fieldName
    let (type, value) ← liftTermElabM <|
      withObjectParams summary.params.toList fun sources codes _ allParams => do
        let source := mkAppN (mkConst summary.typeName) sources
        have owner : Q(TypeId) :=
          mkApp2 (mkConst ``TypeId.mk) (toExpr summary.typeName) (listExpr codes)
        let ownerCode := mkApp (mkConst ``ObjTy.data) owner
        let object ← synthInstance (objectTypeExpr source ownerCode)
        let fieldCodes := constructor.fields.map (fun f => codeTemplateExpr codes f.source)
        have fields : Q(List ObjTy) := listExpr fieldCodes
        have n : Q(Nat) := toExpr i
        let bound ← mkDecideProof q($n < List.length $fields)
        have bound : Q($n < List.length $fields) := bound
        have index : Q(Fin (List.length $fields)) := q(⟨$n, $bound⟩)
        let fieldSource ← sourceTemplateExpr sources field.source
        let fieldCode := fieldCodes[i]!
        let fieldObject ← synthInstance (objectTypeExpr fieldSource fieldCode)
        have ctorName : Q(Name) := toExpr constructor.name
        have reference : Q(IR.CtorRef $owner $fields) := q(⟨$ctorName⟩)
        withLocalDecl `r .implicit (mkConst ``Region) fun r => do
          let input := mkAppN (mkConst ``Val) #[source, r, ownerCode, object]
          withLocalDeclD `value input fun v => do
            let position : Expr := q(IR.Scope.Var.ofIndex Unit (Γ := $fields) $index)
            let expression ← mkAppM ``IR.Tree.Expr.project
              #[reference, position, ← mkAppM ``Val.expr #[v]]
            let result := mkAppN (mkConst ``Val) #[fieldSource, r, fieldCode, fieldObject]
            let body := mkAppN (mkConst ``makeVal) #[fieldSource, r, fieldCode, fieldObject, expression]
            let type ← mkForallFVars (allParams.push r |>.push v) result
            let value ← mkLambdaFVars (allParams.push r |>.push v) body
            pure (type, value)
    liftCoreM <| withExporting do
      addAndCompile (.defnDecl {
        name, levelParams := [], type, value, hints := .regular 1, safety := .safe
      }) (logCompileErrors := true)
    let some field := getFieldInfo? (← getEnv) summary.typeName fieldName | return
    modifyEnv fun env =>
      match ObjectRegistry.find? env summary.typeName with
      | none => env
      | some entry => ObjectRegistry.insert env summary.typeName
          { entry with projections := entry.projections ++ [(field.projFn, name)] }

private def makeEntry (summary : Summary) : ObjectRegistry.ObjectEntry :=
  let names := generatedNames summary.typeName
  { declaration :=
      { name := summary.typeName
        params := summary.params.size
        repr := summary.repr
        constructors := summary.constructors.toList.map fun constructor =>
          { name := constructor.name
            fields := constructor.fields.toList.map fun field =>
              { label := field.label, type := field.source } } }
    idName := names.id
    codeName := names.code
    objectName := names.object
    schemaName := names.schema
    builders := summary.constructors.toList.map fun ctor =>
      (ctor.name, constructorBuilderName summary.typeName ctor.name) }

private def ensureFresh (summary : Summary) : CommandElabM Unit := do
  let env ← getEnv
  if (ObjectRegistry.find? env summary.typeName).isSome then
    throwError "Oria.Object is already derived for {.ofConstName summary.typeName}"
  let names := generatedNames summary.typeName
  let mut targets := #[names.id, names.code, names.object, names.schema]
  for constructor in summary.constructors do
    targets := targets.push (constructorBuilderName summary.typeName constructor.name)
  for target in targets do
    if env.contains target then
      throwError "Oria.Object generated declaration {.ofConstName target} already exists"

private def deriveObject (typeNames : Array Name) : CommandElabM Bool := do
  let some typeName := typeNames[0]? | return false
  unless ← isInductive typeName do
    return false
  let first ← getConstInfoInduct typeName
  let groupNames := first.all.foldl (init := {}) fun names name => names.insert name
  let mut summaries := #[]
  for groupTypeName in first.all do
    let ind ← getConstInfoInduct groupTypeName
    let params ← validate groupTypeName ind
    let constructors ← liftTermElabM <|
      ind.ctors.toArray.mapM
        (inspectConstructor (← getEnv) groupTypeName groupNames ind params)
    let repr := if valueTypeAttribute.hasTag (← getEnv) groupTypeName then .value else .ordinary
    summaries := summaries.push { typeName := groupTypeName, params, constructors, repr }
  for summary in summaries do
    ensureFresh summary
  let mut commands : Array Command := #[]
  for summary in summaries do
    let generated ← withFreshMacroScope <| liftTermElabM <| objectCommands summary
    commands := commands ++ generated
  elabCommand (mkNullNode commands)
  modifyEnv fun env => summaries.foldl (fun env summary =>
    ObjectRegistry.insert env summary.typeName (makeEntry summary)) env
  for summary in summaries do
    addObjectInstance summary
  for summary in summaries do
    for constructor in summary.constructors do
      addConstructor summary constructor
    addProjections summary
  return true

initialize
  registerDerivingHandler ``Oria.Object deriveObject

end Oria.ObjectDerive
