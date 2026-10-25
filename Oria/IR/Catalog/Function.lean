module

public import Oria.Command.Catalog
public import Oria.IR.Tree.Elaborated
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax
import Std.Data.HashSet

namespace Oria.Function

open Oria.IR

private def findDefinition?
    (definitions : List ElaboratedDef) (source : Lean.Name) : Option ElaboratedDef :=
  definitions.find? (fun definition => definition.source == source)

private def referenceName {sig : Signature} (reference : DeclRef sig) : Lean.Name :=
  let .named source := reference.key
  source

private def firstDuplicate? (definitions : List ElaboratedDef) : Option Lean.Name :=
  go {} definitions
where
  go (seen : Std.HashSet Lean.Name) : List ElaboratedDef → Option Lean.Name
    | [] => none
    | definition :: rest =>
        if seen.contains definition.source then
          some definition.source
        else
          go (seen.insert definition.source) rest

private def validateDefinitions (definitions : List ElaboratedDef) : Except Diagnostic Unit := do
  if let some duplicate := firstDuplicate? definitions then
    throw (.duplicateFunction duplicate)

public def CatalogValid (definitions : List ElaboratedDef) : Prop :=
  validateDefinitions definitions = .ok ()

/-- A finite collection of typed, elaborated object functions indexed by source identity. -/
public structure Catalog where
  private mk ::
  private definitions : List ElaboratedDef
  private valid : CatalogValid definitions

namespace Catalog

public def build (definitions : List ElaboratedDef) : Except Diagnostic Catalog :=
  match evidence : validateDefinitions definitions with
  | .ok () => .ok ⟨definitions, evidence⟩
  | .error diagnostic => .error diagnostic

public def Resolves {sig : Signature} (catalog : Catalog) (reference : DeclRef sig) : Prop :=
  ∃ definition,
    ∃ _ : definition.signature = sig,
      findDefinition? catalog.definitions (referenceName reference) = some definition

private def resolve {sig : Signature}
    (catalog : Catalog) (reference : DeclRef sig) :
    Except Diagnostic (PLift (Resolves catalog reference)) :=
  let source := referenceName reference
  match found : findDefinition? catalog.definitions source with
  | none => .error (.unknownFunction source)
  | some definition =>
      if signatureMatches : definition.signature = sig then
        .ok ⟨⟨definition, signatureMatches, found⟩⟩
      else
        .error (.functionSignatureMismatch source definition.signature sig)

private def FunctionsClosedPrim {g : Grade} {a : ObjTy} (catalog : Catalog) :
    IR.Tree.Prim g a → Prop
  | .call reference _ => Resolves catalog reference
  | .execute _ reference _ => Resolves catalog reference
  | .recur _ _ => False
  | .division _ _ | .checkpoint _ | .construct _ _ | .command _ | .memory _ _ => True

mutual
  private def FunctionsClosedRep {g : Grade} {a : ObjTy} (catalog : Catalog) :
      IR.Tree.TreeRep g a → Prop
    | .fail => True
    | .ret _ => True
    | .perform primitive => FunctionsClosedPrim catalog primitive
    | .catching value body => FunctionsClosedRep catalog value ∧ FunctionsClosedRep catalog body
    | .bind _ value body =>
        FunctionsClosedRep catalog value ∧ FunctionsClosedRep catalog body
    | .branch _ yes no =>
        FunctionsClosedRep catalog yes ∧ FunctionsClosedRep catalog no
    | .matchMany _ rows => FunctionsClosedRowsRep catalog rows
    | .scoped _ body => FunctionsClosedRep catalog body
    | .fix _ _ _ _ => False
    | .weaken _ body => FunctionsClosedRep catalog body
    | .block _ body => FunctionsClosedRep catalog body
    | .leave _ _ => True

  private def FunctionsClosedRowRep {types : List ObjTy} {result : ObjTy} {g : Grade}
      (catalog : Catalog) : IR.Tree.RowRep types result g → Prop
    | .mk _ _ body => FunctionsClosedRep catalog body

  private def FunctionsClosedRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade}
      (catalog : Catalog) : IR.Tree.RowsRep types result grades → Prop
    | .nil => True
    | .cons arm rest =>
        FunctionsClosedRowRep catalog arm ∧ FunctionsClosedRowsRep catalog rest
end

public def FunctionsClosed {sig : Signature}
    (catalog : Catalog) (definition : IR.Tree.Def sig) : Prop :=
  FunctionsClosedRep catalog definition.body.rep

private def closePrim {g : Grade} {a : ObjTy} (catalog : Catalog) :
    (primitive : IR.Tree.Prim g a) →
    Except Diagnostic (PLift (FunctionsClosedPrim catalog primitive))
  | .call reference _ => catalog.resolve reference
  | .execute _ reference _ => catalog.resolve reference
  | .recur _ _ => .error .unloweredRecursion
  | .division _ _ | .checkpoint _ | .construct _ _ | .command _ | .memory _ _ => .ok ⟨True.intro⟩

mutual
  private def closeTreeRep {g : Grade} {a : ObjTy} (catalog : Catalog) :
      (body : IR.Tree.TreeRep g a) →
      Except Diagnostic (PLift (FunctionsClosedRep catalog body))
    | .fail => pure ⟨True.intro⟩
    | .ret _ => pure ⟨True.intro⟩
    | .perform primitive => catalog.closePrim primitive
    | .catching value body => do
        let ⟨valueClosed⟩ ← catalog.closeTreeRep value
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨valueClosed, bodyClosed⟩⟩
    | .bind _ value body => do
        let ⟨valueClosed⟩ ← catalog.closeTreeRep value
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨⟨valueClosed, bodyClosed⟩⟩
    | .branch _ yes no => do
        let ⟨yesClosed⟩ ← catalog.closeTreeRep yes
        let ⟨noClosed⟩ ← catalog.closeTreeRep no
        pure ⟨⟨yesClosed, noClosed⟩⟩
    | .matchMany _ rows => catalog.closeRowsRep rows
    | .scoped _ body => catalog.closeTreeRep body
    | .fix _ _ _ _ => .error .unloweredRecursion
    | .weaken _ body => catalog.closeTreeRep body
    | .block _ body => catalog.closeTreeRep body
    | .leave _ _ => pure ⟨True.intro⟩

  private def closeRowRep {types : List ObjTy} {result : ObjTy} {g : Grade} (catalog : Catalog) :
      (arm : IR.Tree.RowRep types result g) →
      Except Diagnostic (PLift (FunctionsClosedRowRep catalog arm))
    | .mk _ _ body => do
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨bodyClosed⟩

  private def closeRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade}
      (catalog : Catalog) :
      (arms : IR.Tree.RowsRep types result grades) →
      Except Diagnostic (PLift (FunctionsClosedRowsRep catalog arms))
    | .nil => pure ⟨True.intro⟩
    | .cons arm rest => do
        let ⟨armClosed⟩ ← catalog.closeRowRep arm
        let ⟨restClosed⟩ ← catalog.closeRowsRep rest
        pure ⟨⟨armClosed, restClosed⟩⟩
end

/-- One Tree definition closed under object, command, and outgoing function references. -/
public structure LinkedDef
    (functions : Catalog)
    (commands : Command.Catalog)
    (objects : ObjectCatalog)
    (sig : Signature) where
  private mk ::
  commandLinked : Command.Catalog.LinkedDef commands objects sig
  functionsClosed : FunctionsClosed functions commandLinked.objectLinked.treeDef

/--
Validate outgoing function references in one definition. A later package entrypoint must invoke
this operation for every catalogue member to establish whole-package recursive closure.
-/
public def link
    {commands : Command.Catalog} {objects : ObjectCatalog} {sig : Signature}
    (catalog : Catalog)
    (definition : Command.Catalog.LinkedDef commands objects sig) :
    Except Diagnostic (LinkedDef catalog commands objects sig) := do
  let ⟨closed⟩ ←
    catalog.closeTreeRep definition.objectLinked.treeDef.body.rep
  pure ⟨definition, closed⟩

end Catalog

end Oria.Function
