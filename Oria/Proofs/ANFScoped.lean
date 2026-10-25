module

import Oria.Compiler.Lower.ANF
import all Oria.IR.Common.Local
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax
meta import Oria.Compiler.Lower.ANF
meta import all Oria.IR.Common.Local
meta import all Oria.IR.Tree.Definition
meta import all Oria.IR.Tree.Syntax

namespace Oria.Proofs.ANFScoped

open Oria Oria.IR

private def compile
    {sig : Signature}
    (source : Lean.Name)
    (definition : Tree.Def sig)
    (schemas : List ObjectSchema := [])
    (routes : List Command.Decl := []) :
    Except Diagnostic (Cont.Def sig) := do
  let objects ← ObjectCatalog.build schemas
  let objectLinked ← objects.link definition
  let commands ← Command.Catalog.build routes
  let commandLinked ← commands.link objectLinked
  let functions ← Function.Catalog.build []
  let linked ← functions.link commandLinked
  Lower.ANF.lower source linked


private def arithmeticSig : Signature := ⟨[], .i32, .pure⟩
private def repeatedSig : Signature := ⟨[.i32, .i32], .i32, .pure⟩

private def repeatedDef : Tree.Def repeatedSig :=
  Tree.Def.build fun
    | .cons _ (.cons right .nil) => pure (.ret right)

#guard
  match compile `repeated repeatedDef with
  | .ok definition =>
      match definition.computation with
      | .ret (.local x) => x.index.val == 1
      | _ => false
  | .error _ => false

private def nestedDef : Tree.Def repeatedSig :=
  Tree.Def.build fun
    | .cons left (.cons right .nil) => do
        Tree.Build.bind (.ret left) fun outer =>
          Tree.Build.bind (.ret (.binary .add outer right)) fun inner =>
            pure (.ret (.binary .add outer inner))

#guard
  match compile `nested nestedDef with
  | .ok definition =>
      match definition.computation with
      | .letOp (.binary .add _ _)
          (.letOp (.binary .add (.local outer) (.local inner)) _) =>
            outer.index.val == 1 && inner.index.val == 0
      | _ => false
  | .error _ => false

private def sharedSig : Signature := ⟨[.i32], .i32, .pure⟩
private def sharedDef : Tree.Def sharedSig :=
  Tree.Def.build fun
    | .cons value .nil =>
        let shared := Tree.Expr.binary .add value (.i32 1)
        pure (.ret (.binary .mul shared shared))

#guard
  match compile `shared sharedDef with
  | .ok definition =>
      match definition.computation with
      | .letOp (.binary .add _ _) (.letOp (.binary .add _ _)
          (.letOp (.binary .mul (.local left) (.local right)) _)) =>
            left.index.val == 1 && right.index.val == 0
      | _ => false
  | .error _ => false

private def firstSlot : Command.SlotKey :=
  ⟨`Oria.Proofs.ANFScoped.first⟩

private def secondSlot : Command.SlotKey :=
  ⟨`Oria.Proofs.ANFScoped.second⟩

private def routeSig : Command.Signature :=
  { schema := [firstSlot, secondSlot]
    req := Req.none
    eff := Eff.none }

private def routeTemplate : Command.Template routeSig.schema :=
  { parts := [
      .slot ⟨0, by simp [routeSig]⟩,
      .space,
      .slot ⟨1, by simp [routeSig]⟩
    ] }

private def routeRef : Command.Ref routeSig :=
  { key := `Oria.Proofs.ANFScoped.command
    template := routeTemplate }

private def routeDecl : Command.Decl :=
  { key := routeRef.key
    sig := routeSig
    template := routeTemplate }

private def commandSig : Signature :=
  { args := [.i32, .i32]
    result := .i32
    grade := routeSig.grade }

private def commandDef : Tree.Def commandSig :=
  Tree.Def.build fun
    | .cons left (.cons right .nil) => do
        let request : Command.Call Tree.Expr routeSig := {
          ref := routeRef
          args :=
            .cons
              ⟨Command.Fragment.spaced [
                Command.Fragment.hole .i32 left,
                Command.Fragment.hole .i32 right
              ]⟩
              (.cons ⟨Command.Fragment.hole .i32 left⟩ .nil)
        }
        have same : request.grade = commandSig.grade := by
          simp [request, Command.Call.grade, Command.Call.requirements,
            Command.EncodedArg.requirements, commandSig, routeSig, Command.Signature.grade, Req.none]
        pure (.perform (same ▸ Tree.Prim.command request))


private def holeIndices {context : List ObjTy} {sig : Command.Signature}
    (request : Command.Call (Cont.Atom context) sig) : List Nat :=
  request.traverseK
    (fun value next => match value with
      | .local x => x.index.val :: next value
      | _ => next value)
    (fun _ => [])

#guard
  match compile `command commandDef [] [routeDecl] with
  | .ok definition =>
      match definition.computation with
      | .invoke (.command request) _ .fail => holeIndices request == [0, 1, 0]
      | _ => false
  | .error _ => false

private def stray : Local ObjTy.i32 :=
  Local.fresh 100

private def unboundDef : Tree.Def arithmeticSig :=
  ⟨.nil, ⟨.ret (.local stray)⟩⟩

private def duplicate : Local ObjTy.i32 :=
  Local.fresh 200

private def ambiguousDef : Tree.Def repeatedSig :=
  ⟨.cons duplicate (.cons duplicate .nil),
    ⟨.ret (.local duplicate)⟩⟩

/- A malformed occurrence outside the parameter telescope receives a typed scope diagnostic. -/
#guard
  match compile `Oria.Proofs.ANFScoped.unbound unboundDef with
  | .error (.invalidLocalScope source .i32 .unbound) =>
      source == `Oria.Proofs.ANFScoped.unbound
  | _ => false

/- An ambiguous nominal scope produces its dedicated diagnostic. -/
#guard
  match compile `Oria.Proofs.ANFScoped.ambiguous ambiguousDef with
  | .error (.invalidLocalScope source .i32 .ambiguous) =>
      source == `Oria.Proofs.ANFScoped.ambiguous
  | _ => false


end Oria.Proofs.ANFScoped
