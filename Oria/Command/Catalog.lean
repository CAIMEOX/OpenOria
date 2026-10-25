module

public import Oria.IR.Catalog.Object
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax
import Std.Data.HashSet

namespace Oria.Command

open Oria.IR

private def findDecl? (decls : List Decl) (key : Lean.Name) : Option Decl :=
  decls.find? (fun decl => decl.key == key)

private def firstDuplicate? (decls : List Decl) : Option Lean.Name :=
  go {} decls
where
  go (seen : Std.HashSet Lean.Name) : List Decl → Option Lean.Name
    | [] => none
    | decl :: rest =>
        if seen.contains decl.key then some decl.key else go (seen.insert decl.key) rest

private def firstInvalidTemplate? (decls : List Decl) : Option Lean.Name :=
  decls.findSome? fun decl =>
    if decl.template.valid then none else some decl.key

private def validateDecls (decls : List Decl) : Except Diagnostic Unit := do
  if let some duplicate := firstDuplicate? decls then
    throw (.duplicateCommand duplicate)
  if let some invalid := firstInvalidTemplate? decls then
    throw (.invalidCommandTemplate invalid)
  pure ()

public def CatalogValid (decls : List Decl) : Prop :=
  validateDecls decls = .ok ()

/-- A nominal command catalogue. Concrete target capability checks remain a later stage. -/
public structure Catalog where
  private mk ::
  private decls : List Decl
  private valid : CatalogValid decls

namespace Catalog

@[expose] public def lookup? (catalog : Catalog) (key : Lean.Name) : Option Decl :=
  private_decl% (findDecl? catalog.decls key)

public def build (decls : List Decl) : Except Diagnostic Catalog :=
  match evidence : validateDecls decls with
  | .ok () => .ok ⟨decls, evidence⟩
  | .error diagnostic => .error diagnostic

public def ResolvesRef {sig : Signature} (catalog : Catalog) (ref : Ref sig) : Prop :=
  ∃ decl,
    ∃ signatureMatches : decl.sig = sig,
      catalog.lookup? ref.key = some decl ∧
        signatureMatches ▸ decl.template = ref.template

/-- Computational typed decl lookup retaining the exact declaration and both equalities. -/
public structure ResolvedRef {sig : Signature} (catalog : Catalog) (ref : Ref sig) where
  decl : Decl
  signatureMatches : decl.sig = sig
  found : catalog.lookup? ref.key = some decl
  templateMatches : signatureMatches ▸ decl.template = ref.template

namespace ResolvedRef
public theorem sound {catalog : Catalog} {sig : Signature} {ref : Ref sig}
    (resolved : ResolvedRef catalog ref) : ResolvesRef catalog ref :=
  ⟨resolved.decl, resolved.signatureMatches, resolved.found, resolved.templateMatches⟩
end ResolvedRef

public abbrev Resolves {f : ObjTy → Type} {sig : Signature} (catalog : Catalog) (request : Call f sig) : Prop :=
  ResolvesRef catalog request.ref

public def resolveRef {sig : Signature}
    (catalog : Catalog) (ref : Ref sig) :
    Except Diagnostic (ResolvedRef catalog ref) :=
  match found : catalog.lookup? ref.key with
  | none => .error (.unknownCommand ref.key)
  | some decl =>
      if signatureMatches : decl.sig = sig then
        let template := signatureMatches ▸ decl.template
        if templateMatches : template = ref.template then
          .ok ⟨decl, signatureMatches, found, templateMatches⟩
        else
          .error (.commandTemplateMismatch ref.key)
      else
        .error (.commandSignatureMismatch ref.key)

public def resolve {f : ObjTy → Type} {sig : Signature}
    (catalog : Catalog) (request : Call f sig) :
    Except Diagnostic (PLift (Resolves catalog request)) := do
  let resolved ← catalog.resolveRef request.ref
  pure ⟨resolved.sound⟩

/-- Include an internally required command, checking an existing declaration against its full reference. -/
public def add {sig : Signature} (catalog : Catalog) (ref : Ref sig) : Except Diagnostic Catalog := do
  if (catalog.lookup? ref.key).isSome then
    discard (catalog.resolveRef ref)
    pure catalog
  else build (catalog.decls ++ [ref.declaration])

private def CommandsClosedPrim {g : Grade} {a : ObjTy} (catalog : Catalog) : IR.Tree.Prim g a → Prop
  | .command request => Resolves catalog request
  | .division _ _ | .checkpoint _ | .construct _ _ | .call _ _ | .recur _ _ | .execute _ _ _ | .memory _ _ => True

mutual
  private def CommandsClosedRep {g : Grade} {a : ObjTy} (catalog : Catalog) : IR.Tree.TreeRep g a → Prop
    | .fail => True
    | .ret _ => True
    | .perform primitive => CommandsClosedPrim catalog primitive
    | .catching value body => CommandsClosedRep catalog value ∧ CommandsClosedRep catalog body
    | .bind _ value body =>
        CommandsClosedRep catalog value ∧ CommandsClosedRep catalog body
    | .branch _ yes no =>
        CommandsClosedRep catalog yes ∧ CommandsClosedRep catalog no
    | .matchMany _ rows => CommandsClosedRowsRep catalog rows
    | .scoped _ body => CommandsClosedRep catalog body
    | .fix _ _ body _ => CommandsClosedRep catalog body
    | .weaken _ body => CommandsClosedRep catalog body
    | .block _ body => CommandsClosedRep catalog body
    | .leave _ _ => True

  private def CommandsClosedRowRep
      {types : List ObjTy} {result : ObjTy} {g : Grade}
      (catalog : Catalog) : IR.Tree.RowRep types result g → Prop
    | .mk _ _ body => CommandsClosedRep catalog body

  private def CommandsClosedRowsRep
      {types : List ObjTy} {result : ObjTy} {grades : List Grade}
      (catalog : Catalog) : IR.Tree.RowsRep types result grades → Prop
    | .nil => True
    | .cons arm rest =>
        CommandsClosedRowRep catalog arm ∧ CommandsClosedRowsRep catalog rest
end

public def CommandsClosed
    {sig : Oria.Signature} (catalog : Catalog) (definition : IR.Tree.Def sig) : Prop :=
  CommandsClosedRep catalog definition.body.rep

private def closePrim {g : Grade} {a : ObjTy} (catalog : Catalog) :
    (primitive : IR.Tree.Prim g a) →
    Except Diagnostic (PLift (CommandsClosedPrim catalog primitive))
  | .command request => catalog.resolve request
  | .division _ _ | .checkpoint _ | .construct _ _ | .call _ _ | .recur _ _ | .execute _ _ _ | .memory _ _ => .ok ⟨True.intro⟩

mutual
  private def closeTreeRep {g : Grade} {a : ObjTy} (catalog : Catalog) :
      (body : IR.Tree.TreeRep g a) →
      Except Diagnostic (PLift (CommandsClosedRep catalog body))
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
    | .fix _ _ body _ => catalog.closeTreeRep body
    | .weaken _ body => catalog.closeTreeRep body
    | .block _ body => catalog.closeTreeRep body
    | .leave _ _ => pure ⟨True.intro⟩

  private def closeRowRep {types : List ObjTy} {result : ObjTy} {g : Grade} (catalog : Catalog) :
      (arm : IR.Tree.RowRep types result g) →
      Except Diagnostic (PLift (CommandsClosedRowRep catalog arm))
    | .mk _ _ body => do
        let ⟨bodyClosed⟩ ← catalog.closeTreeRep body
        pure ⟨bodyClosed⟩

  private def closeRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade} (catalog : Catalog) :
      (arms : IR.Tree.RowsRep types result grades) →
      Except Diagnostic (PLift (CommandsClosedRowsRep catalog arms))
    | .nil => pure ⟨True.intro⟩
    | .cons arm rest => do
        let ⟨armClosed⟩ ← catalog.closeRowRep arm
        let ⟨restClosed⟩ ← catalog.closeRowsRep rest
        pure ⟨⟨armClosed, restClosed⟩⟩
end

public structure LinkedDef
    (catalog : Catalog) (objects : ObjectCatalog) (sig : Oria.Signature) where
  private mk ::
  objectLinked : ObjectCatalog.LinkedDef objects sig
  commandsClosed : CommandsClosed catalog objectLinked.treeDef

public def link
    {objects : ObjectCatalog} {sig : Oria.Signature}
    (catalog : Catalog) (definition : ObjectCatalog.LinkedDef objects sig) :
    Except Diagnostic (LinkedDef catalog objects sig) := do
  let ⟨closed⟩ ← catalog.closeTreeRep definition.treeDef.body.rep
  pure ⟨definition, closed⟩

end Catalog

end Oria.Command
