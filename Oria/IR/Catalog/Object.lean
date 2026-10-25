module

public import Oria.Diagnostic
public import Oria.IR.Tree.Definition
public import Oria.IR.Common.Schema
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax
import Std.Data.HashSet

namespace Oria

open IR

private def findSchema? (schemas : List ObjectSchema) (id : TypeId) : Option ObjectSchema :=
  schemas.find? (fun schema => schema.id == id)

private def ObjectSchema.localValid (schema : ObjectSchema) : Bool :=
  let namesUnique := decide (schema.constructors.map (·.name)).Nodup
  !schema.constructors.isEmpty && namesUnique

private def fieldResolved (schemas : List ObjectSchema) : ObjTy → Bool
  | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => true
  | .option a | .ref a => fieldResolved schemas a
  | .data id => (findSchema? schemas id).isSome

private def firstMissingType? (schemas : List ObjectSchema) (schema : ObjectSchema) :
    Option TypeId :=
  schema.constructors.findSome? fun constructor =>
    constructor.fields.findSome? (firstMissingInType schemas)
where
  firstMissingInType (schemas : List ObjectSchema) : ObjTy → Option TypeId
    | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => none
    | .option a | .ref a => firstMissingInType schemas a
    | .data id => if (findSchema? schemas id).isSome then none else some id

private def schemaFieldsValid (schemas : List ObjectSchema) (schema : ObjectSchema) : Bool :=
  schema.constructors.all fun constructor =>
    constructor.fields.all (fieldResolved schemas)

private def firstDuplicate? (values : List TypeId) : Option TypeId :=
  go {} values
where
  go (seen : Std.HashSet TypeId) : List TypeId → Option TypeId
    | [] => none
    | value :: rest =>
        if seen.contains value then some value else go (seen.insert value) rest

private def validateSchemas (schemas : List ObjectSchema) : Except Diagnostic Unit := do
  let ids := schemas.map (·.id)
  if let some duplicate := firstDuplicate? ids then
    throw (.duplicateObjectType duplicate)
  for schema in schemas do
    unless schema.localValid do
      throw (.invalidObjectSchema schema.id)
    if let some missing := firstMissingType? schemas schema then
      throw (.unresolvedObjectType schema.id missing)
    unless schemaFieldsValid schemas schema do
      throw (.invalidObjectSchema schema.id)

/-- Kernel proposition carried by a certified catalogue. -/
public def CatalogValid (schemas : List ObjectSchema) : Prop :=
  validateSchemas schemas = .ok ()

/-- A source-erased, reference-closed collection of object schemas. -/
public structure ObjectCatalog where
  private mk ::
  private schemas : List ObjectSchema
  private valid : CatalogValid schemas

namespace ObjectCatalog

/-- Resolve the logical constructor family used by pattern compilation. -/
public def schema? (catalog : ObjectCatalog) (id : TypeId) : Option ObjectSchema :=
  findSchema? catalog.schemas id

/--
Validate explicit low-level schemas, nominal uniqueness, and all field references.

This is the raw IR seam. Source-language/package compilation freezes the corresponding schema
list from deriving registry entries rather than accepting arbitrary source-type claims.
-/
public def build (schemas : List ObjectSchema) : Except Diagnostic ObjectCatalog :=
  match evidence : validateSchemas schemas with
  | .ok () => .ok ⟨schemas, evidence⟩
  | .error diagnostic => .error diagnostic

public def Resolves
    (catalog : ObjectCatalog) {owner : TypeId} {fields : List ObjTy}
    (reference : CtorRef owner fields) : Prop :=
  ∃ schema,
    catalog.schemas.find? (fun candidate => candidate.id == owner) = some schema ∧
    ∃ constructor,
      schema.constructors.find? (fun ctor => ctor.name == reference.name) =
        some constructor ∧
      constructor.fields = fields

private def resolve
    (catalog : ObjectCatalog) {owner : TypeId} {fields : List ObjTy}
    (reference : CtorRef owner fields) :
    Except Diagnostic (PLift (Resolves catalog reference)) :=
  match schemaFound : catalog.schemas.find? (fun candidate => candidate.id == owner) with
  | none => .error (.unknownConstructor owner reference.name)
  | some schema =>
      match constructorFound :
          schema.constructors.find? (fun ctor => ctor.name == reference.name) with
      | none => .error (.unknownConstructor owner reference.name)
      | some constructor =>
          if fieldsMatch : constructor.fields = fields then
            .ok ⟨⟨schema, schemaFound, constructor, constructorFound, fieldsMatch⟩⟩
          else
            .error (.constructorShapeMismatch
              owner reference.name constructor.fields fields)

/-- A total projection resolves to the sole constructor and its exact field telescope. -/
public def RecordClosed (catalog : ObjectCatalog) {owner : TypeId} {fields : List ObjTy}
    (reference : CtorRef owner fields) : Prop :=
  ∃ schema, findSchema? catalog.schemas owner = some schema ∧
    schema.constructors = [{ name := reference.name, fields }]

private def closeRecord (catalog : ObjectCatalog) {owner : TypeId} {fields : List ObjTy}
    (reference : CtorRef owner fields) : Except Diagnostic (PLift (RecordClosed catalog reference)) :=
  match found : findSchema? catalog.schemas owner with
  | none => .error (.unknownObjectType owner)
  | some schema =>
    if shape : schema.constructors = [{ name := reference.name, fields }] then
      .ok ⟨⟨schema, found, shape⟩⟩
    else .error (.invalidObjectSchema owner)

/-- A logical type is primitive or resolves to exactly one schema in the catalogue. -/
public def TypeClosed (catalog : ObjectCatalog) : ObjTy → Prop
  | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => True
  | .option element | .ref element =>
      TypeClosed catalog element
  | .data id => ∃ schema, findSchema? catalog.schemas id = some schema

private def TypesClosedList (catalog : ObjectCatalog) : List ObjTy → Prop
  | [] => True
  | ty :: types => TypeClosed catalog ty ∧ TypesClosedList catalog types

public def SignatureTypesClosed (catalog : ObjectCatalog) (sig : Signature) : Prop :=
  TypesClosedList catalog sig.args ∧ TypeClosed catalog sig.result

private def ExprTypeClosed {a : ObjTy} (catalog : ObjectCatalog) : IR.Tree.Expr a → Prop
  | .local _ | .unit | .bool _ | .i32 _ => TypeClosed catalog a
  | .unary _ value => TypeClosed catalog a ∧ ExprTypeClosed catalog value
  | .binary _ left right =>
      TypeClosed catalog a ∧ ExprTypeClosed catalog left ∧ ExprTypeClosed catalog right
  | .ite condition yes no => TypeClosed catalog a ∧ ExprTypeClosed catalog condition ∧
      ExprTypeClosed catalog yes ∧ ExprTypeClosed catalog no
  | .project constructor _ value =>
      TypeClosed catalog a ∧ RecordClosed catalog constructor ∧ ExprTypeClosed catalog value

private def ExprsTypesClosed {types : List ObjTy}
    (catalog : ObjectCatalog) (expressions : Args IR.Tree.Expr types) :
    Prop :=
  expressions.All (ExprTypeClosed catalog)

private def ConstructorClosed {a : ObjTy} {fields : List ObjTy} (catalog : ObjectCatalog) :
    IR.Constructor a fields → Prop
  | .data reference => Resolves catalog reference
  | .none | .some => True


private def ConstructorsClosedPrim {g : Grade} {a : ObjTy}
    (catalog : ObjectCatalog) : IR.Tree.Prim g a → Prop
  | .construct reference _ => ConstructorClosed catalog reference
  | .division _ _ | .checkpoint _ | .call _ _ | .recur _ _ | .execute _ _ _ | .command _ | .memory _ _ => True

private def TypesClosedPrim {g : Grade} {a : ObjTy} (catalog : ObjectCatalog) :
    IR.Tree.Prim g a → Prop
  | .division left right => ExprTypeClosed catalog left ∧ ExprTypeClosed catalog right
  | .checkpoint _ => True
  | .construct (a := a) (fields := fields) _ arguments
  | .memory (a := a) (fields := fields) _ arguments =>
      TypeClosed catalog a ∧
      TypesClosedList catalog fields ∧ ExprsTypesClosed catalog arguments
  | .call (sig := sig) _ arguments | .recur (sig := sig) _ arguments =>
      SignatureTypesClosed catalog sig ∧ ExprsTypesClosed catalog arguments
  | .command request => request.All (ExprTypeClosed catalog)
  | .execute (params := params) (g := g) scope _ arguments =>
      SignatureTypesClosed catalog ⟨params, .i32, g⟩ ∧
        ExprsTypesClosed catalog arguments ∧ scope.fragment.All (ExprTypeClosed catalog)


mutual
  private def PatternClosed {a : ObjTy} {bindings : List ObjTy} (catalog : ObjectCatalog) :
      IR.Tree.Pattern a bindings → Prop
    | .any | .bind => TypeClosed catalog a
    | .i32 _ => TypeClosed catalog .i32
    | .ctor constructor fields =>
        TypeClosed catalog a ∧ ConstructorClosed catalog constructor ∧
          PatternsClosed catalog fields

  private def PatternsClosed {types : List ObjTy} {bindings : List ObjTy} (catalog : ObjectCatalog) :
      IR.Tree.Patterns types bindings → Prop
    | .nil => True
    | .cons head rest => PatternClosed catalog head ∧ PatternsClosed catalog rest
end

mutual
  private def ConstructorsClosedRep {g : Grade} {a : ObjTy}
      (catalog : ObjectCatalog) : IR.Tree.TreeRep g a → Prop
    | .fail => True
    | .ret _ => True
    | .perform primitive => ConstructorsClosedPrim catalog primitive
    | .catching value body => ConstructorsClosedRep catalog value ∧ ConstructorsClosedRep catalog body
    | .bind _ value body =>
        ConstructorsClosedRep catalog value ∧ ConstructorsClosedRep catalog body
    | .branch _ yes no =>
        ConstructorsClosedRep catalog yes ∧ ConstructorsClosedRep catalog no
    | .matchMany _ rows => ConstructorsClosedRowsRep catalog rows
    | .scoped _ body => ConstructorsClosedRep catalog body
    | .fix _ _ body _ => ConstructorsClosedRep catalog body
    | .weaken _ body => ConstructorsClosedRep catalog body
    | .block _ body => ConstructorsClosedRep catalog body
    | .leave _ _ => True

  private def ConstructorsClosedRowRep {types : List ObjTy} {result : ObjTy} {g : Grade}
      (catalog : ObjectCatalog) : IR.Tree.RowRep types result g → Prop
    | .mk patterns _ body =>
        PatternsClosed catalog patterns ∧ ConstructorsClosedRep catalog body

  private def ConstructorsClosedRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade}
      (catalog : ObjectCatalog) : IR.Tree.RowsRep types result grades → Prop
    | .nil => True
    | .cons row rest =>
        ConstructorsClosedRowRep catalog row ∧ ConstructorsClosedRowsRep catalog rest
end

mutual
  private def TypesClosedRep {g : Grade} {a : ObjTy}
      (catalog : ObjectCatalog) : IR.Tree.TreeRep g a → Prop
    | .fail => TypeClosed catalog a
    | .ret expression => ExprTypeClosed catalog expression
    | .perform primitive => TypesClosedPrim catalog primitive
    | .catching value body => TypesClosedRep catalog value ∧ TypesClosedRep catalog body
    | .bind _ value body => TypesClosedRep catalog value ∧ TypesClosedRep catalog body
    | .branch condition yes no =>
        ExprTypeClosed catalog condition ∧ TypesClosedRep catalog yes ∧ TypesClosedRep catalog no
    | .matchMany values rows => ExprsTypesClosed catalog values ∧ TypesClosedRowsRep catalog rows
    | .scoped scope body => scope.fragment.All (ExprTypeClosed catalog) ∧ TypesClosedRep catalog body
    | .fix (sig := sig) _ _ body args =>
        SignatureTypesClosed catalog sig ∧ TypesClosedRep catalog body ∧ ExprsTypesClosed catalog args
    | .weaken _ body => TypesClosedRep catalog body
    | .block _ body => TypesClosedRep catalog body
    | .leave _ value => TypeClosed catalog a ∧ ExprTypeClosed catalog value

  private def TypesClosedRowRep {types : List ObjTy} {result : ObjTy} {g : Grade}
      (catalog : ObjectCatalog) : IR.Tree.RowRep types result g → Prop
    | .mk (bindings := bindings) _ _ body =>
        TypesClosedList catalog bindings ∧ TypesClosedRep catalog body

  private def TypesClosedRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade}
      (catalog : ObjectCatalog) : IR.Tree.RowsRep types result grades → Prop
    | .nil => True
    | .cons row rest => TypesClosedRowRep catalog row ∧ TypesClosedRowsRep catalog rest
end

/-- Every nominal constructor claim resolves with its exact indexed telescope. -/
public def ConstructorsClosed {g : Grade} {a : ObjTy}
    (catalog : ObjectCatalog) (tree : IR.Tree.Tree g a) : Prop :=
  ConstructorsClosedRep catalog tree.rep

/-- Every logical type mentioned by a Tree resolves in the object catalogue. -/
public def TypesClosed {g : Grade} {a : ObjTy}
    (catalog : ObjectCatalog) (tree : IR.Tree.Tree g a) : Prop :=
  TypesClosedRep catalog tree.rep

public def DefinitionTypesClosed {sig : Signature}
    (catalog : ObjectCatalog) (definition : IR.Tree.Def sig) : Prop :=
  TypesClosed catalog definition.body

public def DefinitionConstructorsClosed {sig : Signature}
    (catalog : ObjectCatalog) (definition : IR.Tree.Def sig) : Prop :=
  ConstructorsClosed catalog definition.body

private def closeType (catalog : ObjectCatalog) :
    (ty : ObjTy) → Except Diagnostic (PLift (TypeClosed catalog ty))
  | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => .ok ⟨True.intro⟩
  | .option element | .ref element => catalog.closeType element
  | .data id =>
      match found : findSchema? catalog.schemas id with
      | none => .error (.unknownObjectType id)
      | some schema => .ok ⟨⟨schema, found⟩⟩

private def closeTypes (catalog : ObjectCatalog) :
    (types : List ObjTy) → Except Diagnostic (PLift (TypesClosedList catalog types))
  | [] => .ok ⟨True.intro⟩
  | ty :: types => do
      let ⟨typeClosed⟩ ← catalog.closeType ty
      let ⟨typesClosed⟩ ← catalog.closeTypes types
      pure ⟨⟨typeClosed, typesClosed⟩⟩

private def closeSignature
    (catalog : ObjectCatalog) (sig : Signature) :
    Except Diagnostic (PLift (SignatureTypesClosed catalog sig)) := do
  let ⟨argsClosed⟩ ← catalog.closeTypes sig.args
  let ⟨resultClosed⟩ ← catalog.closeType sig.result
  pure ⟨⟨argsClosed, resultClosed⟩⟩

private def closeExpr {a : ObjTy}
    (catalog : ObjectCatalog) : (expression : IR.Tree.Expr a) →
    Except Diagnostic (PLift (ExprTypeClosed catalog expression))
  | .local _ => catalog.closeType a
  | .unit | .bool _ | .i32 _ => pure ⟨True.intro⟩
  | .unary _ value => do
    let ⟨type⟩ ← catalog.closeType a
    let ⟨value⟩ ← catalog.closeExpr value
    pure ⟨type, value⟩
  | .binary _ left right => do
    let ⟨type⟩ ← catalog.closeType a
    let ⟨left⟩ ← catalog.closeExpr left
    let ⟨right⟩ ← catalog.closeExpr right
    pure ⟨type, left, right⟩
  | .ite condition yes no => do
    let ⟨type⟩ ← catalog.closeType a
    let ⟨condition⟩ ← catalog.closeExpr condition
    let ⟨yes⟩ ← catalog.closeExpr yes
    let ⟨no⟩ ← catalog.closeExpr no
    pure ⟨type, condition, yes, no⟩
  | .project constructor _ value => do
    let ⟨type⟩ ← catalog.closeType a
    let ⟨record⟩ ← catalog.closeRecord constructor
    let ⟨value⟩ ← catalog.closeExpr value
    pure ⟨type, record, value⟩

private def closeExprs {types : List ObjTy}
    (catalog : ObjectCatalog) (expressions : Args IR.Tree.Expr types) :
    Except Diagnostic (PLift (ExprsTypesClosed catalog expressions)) :=
  expressions.proveAll catalog.closeExpr

private def closeConstructor {a : ObjTy} {fields : List ObjTy} (catalog : ObjectCatalog) :
    (constructor : IR.Constructor a fields) →
      Except Diagnostic (PLift (ConstructorClosed catalog constructor))
  | .data reference => catalog.resolve reference
  | .none | .some => pure ⟨True.intro⟩


private def closePrim {g : Grade} {a : ObjTy} (catalog : ObjectCatalog) :
    (primitive : IR.Tree.Prim g a) → Except Diagnostic (PLift (
      ConstructorsClosedPrim catalog primitive ∧ TypesClosedPrim catalog primitive))
  | .division left right => do
      let ⟨leftClosed⟩ ← catalog.closeExpr left
      let ⟨rightClosed⟩ ← catalog.closeExpr right
      pure ⟨⟨True.intro, leftClosed, rightClosed⟩⟩
  | .checkpoint _ => pure ⟨⟨True.intro, True.intro⟩⟩
  | .construct (a := a) (fields := fields) reference arguments => do
      let ⟨resolved⟩ ← catalog.closeConstructor reference
      let ⟨ownerClosed⟩ ← catalog.closeType a
      let ⟨fieldsClosed⟩ ← catalog.closeTypes fields
      let ⟨argumentsClosed⟩ ← catalog.closeExprs arguments
      pure ⟨⟨resolved, ownerClosed, fieldsClosed, argumentsClosed⟩⟩
  | .call (sig := sig) _ arguments | .recur (sig := sig) _ arguments => do
      let ⟨signatureClosed⟩ ← catalog.closeSignature sig
      let ⟨argumentsClosed⟩ ← catalog.closeExprs arguments
      pure ⟨⟨True.intro, signatureClosed, argumentsClosed⟩⟩
  | .command request => do
      let ⟨argumentsClosed⟩ ← request.proveAll catalog.closeExpr
      pure ⟨⟨True.intro, argumentsClosed⟩⟩
  | .execute (params := params) (g := g) scope _ arguments => do
      let ⟨signatureClosed⟩ ← catalog.closeSignature ⟨params, .i32, g⟩
      let ⟨argumentsClosed⟩ ← catalog.closeExprs arguments
      let ⟨holesClosed⟩ ← scope.fragment.proveAll catalog.closeExpr
      pure ⟨⟨True.intro, signatureClosed, argumentsClosed, holesClosed⟩⟩
  | .memory (a := a) (fields := fields) _ arguments => do
      let ⟨ownerClosed⟩ ← catalog.closeType a
      let ⟨fieldsClosed⟩ ← catalog.closeTypes fields
      let ⟨argumentsClosed⟩ ← catalog.closeExprs arguments
      pure ⟨⟨True.intro, ownerClosed, fieldsClosed, argumentsClosed⟩⟩



mutual
  private def closePattern {a : ObjTy} {bindings : List ObjTy} (catalog : ObjectCatalog) :
      (pattern : IR.Tree.Pattern a bindings) →
        Except Diagnostic (PLift (PatternClosed catalog pattern))
    | .any | .bind => catalog.closeType a
    | .i32 _ => catalog.closeType .i32
    | .ctor constructor fields => do
        let ⟨typeClosed⟩ ← catalog.closeType a
        let ⟨constructorClosed⟩ ← catalog.closeConstructor constructor
        let ⟨fieldsClosed⟩ ← catalog.closePatterns fields
        pure ⟨⟨typeClosed, constructorClosed, fieldsClosed⟩⟩

  private def closePatterns {types : List ObjTy} {bindings : List ObjTy} (catalog : ObjectCatalog) :
      (patterns : IR.Tree.Patterns types bindings) →
        Except Diagnostic (PLift (PatternsClosed catalog patterns))
    | .nil => pure ⟨True.intro⟩
    | .cons head rest => do
        let ⟨headClosed⟩ ← catalog.closePattern head
        let ⟨restClosed⟩ ← catalog.closePatterns rest
        pure ⟨⟨headClosed, restClosed⟩⟩
end

private structure BodyClosed {g : Grade} {a : ObjTy}
    (catalog : ObjectCatalog) (body : IR.Tree.TreeRep g a) : Prop where
  constructors : ConstructorsClosedRep catalog body
  types : TypesClosedRep catalog body

mutual
  private def closeTreeRep {g : Grade} {a : ObjTy} (catalog : ObjectCatalog) :
      (body : IR.Tree.TreeRep g a) → Except Diagnostic (PLift (BodyClosed catalog body))
    | .fail => do
        let ⟨closed⟩ ← catalog.closeType a
        pure ⟨⟨True.intro, closed⟩⟩
    | .ret expression => do
        let ⟨closed⟩ ← catalog.closeExpr expression
        pure ⟨⟨True.intro, closed⟩⟩
    | .perform primitive => do
        let ⟨constructors, types⟩ ← catalog.closePrim primitive
        pure ⟨⟨constructors, types⟩⟩
    | .catching value body => do
        let ⟨valueClosed⟩ ← catalog.closeTreeRep value
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨⟨valueClosed.constructors, bodyClosed.constructors⟩,
          ⟨valueClosed.types, bodyClosed.types⟩⟩⟩
    | .bind _ value body => do
        let ⟨valueClosed⟩ ← catalog.closeTreeRep value
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨⟨valueClosed.constructors, bodyClosed.constructors⟩,
          ⟨valueClosed.types, bodyClosed.types⟩⟩⟩
    | .branch condition yes no => do
        let ⟨conditionClosed⟩ ← catalog.closeExpr condition
        let ⟨yesClosed⟩ ← catalog.closeTreeRep yes
        let ⟨noClosed⟩ ← catalog.closeTreeRep no
        pure ⟨⟨⟨yesClosed.constructors, noClosed.constructors⟩,
          ⟨conditionClosed, yesClosed.types, noClosed.types⟩⟩⟩
    | .matchMany values rows => do
        let ⟨valuesClosed⟩ ← catalog.closeExprs values
        let ⟨constructors, types⟩ ← catalog.closeRowsRep rows
        pure ⟨⟨constructors, valuesClosed, types⟩⟩
    | .scoped scope body => do
        let ⟨holesClosed⟩ ← scope.fragment.proveAll catalog.closeExpr
        let ⟨closed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨closed.constructors, holesClosed, closed.types⟩⟩
    | .fix (sig := sig) _ _ body args => do
        let ⟨signatureClosed⟩ ← catalog.closeSignature sig
        let ⟨closed⟩ ← catalog.closeTreeRep body
        let ⟨argumentsClosed⟩ ← catalog.closeExprs args
        pure ⟨⟨closed.constructors, signatureClosed, closed.types, argumentsClosed⟩⟩
    | .weaken _ body => do
        let ⟨closed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨closed.constructors, closed.types⟩⟩
    | .block _ body => do
        let ⟨closed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨closed.constructors, closed.types⟩⟩
    | .leave _ value => do
        let ⟨type⟩ ← catalog.closeType a
        let ⟨closed⟩ ← catalog.closeExpr value
        pure ⟨⟨True.intro, type, closed⟩⟩

  private def closeRowRep {types : List ObjTy} {result : ObjTy} {g : Grade} (catalog : ObjectCatalog) :
      (row : IR.Tree.RowRep types result g) → Except Diagnostic (PLift (
        ConstructorsClosedRowRep catalog row ∧ TypesClosedRowRep catalog row))
    | .mk (bindings := bindings) patterns _ body => do
        let ⟨patternsClosed⟩ ← catalog.closePatterns patterns
        let ⟨bindingsClosed⟩ ← catalog.closeTypes bindings
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨⟨patternsClosed, bodyClosed.constructors⟩,
          ⟨bindingsClosed, bodyClosed.types⟩⟩⟩

  private def closeRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade}
      (catalog : ObjectCatalog) :
      (rows : IR.Tree.RowsRep types result grades) → Except Diagnostic (PLift (
        ConstructorsClosedRowsRep catalog rows ∧ TypesClosedRowsRep catalog rows))
    | .nil => pure ⟨⟨True.intro, True.intro⟩⟩
    | .cons row rest => do
        let ⟨rowConstructors, rowTypes⟩ ← catalog.closeRowRep row
        let ⟨restConstructors, restTypes⟩ ← catalog.closeRowsRep rest
        pure ⟨⟨⟨rowConstructors, restConstructors⟩, ⟨rowTypes, restTypes⟩⟩⟩
end

/-- Object identities and constructor telescopes used by a source definition. -/
public structure CatalogClosed
    (catalog : ObjectCatalog) (sig : Signature) (definition : IR.Tree.Def sig) : Prop where
  signatureTypesClosed : SignatureTypesClosed catalog sig
  typesClosed : DefinitionTypesClosed catalog definition
  constructorsClosed : DefinitionConstructorsClosed catalog definition

/-- Structured Tree with catalogue-closed object identities. -/
public structure LinkedDef (catalog : ObjectCatalog) (sig : Signature) where
  private mk ::
  treeDef : IR.Tree.Def sig
  catalogClosed : CatalogClosed catalog sig treeDef

/-- Validate logical types and constructor references before pattern compilation. -/
public def link {sig : Signature} (catalog : ObjectCatalog) (definition : IR.Tree.Def sig) :
    Except Diagnostic (LinkedDef catalog sig) := do
  let ⟨signatureClosed⟩ ← catalog.closeSignature sig
  let ⟨bodyClosed⟩ ← catalog.closeTreeRep definition.body.rep
  pure ⟨definition, ⟨signatureClosed, bodyClosed.types, bodyClosed.constructors⟩⟩

end ObjectCatalog
end Oria
