module

public import Oria.IR.Tree.Elaborated
import all Oria.IR.Tree.Elaborated
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax

namespace Oria.Lower.Scope

open Oria.IR Oria.IR.Tree

public structure Lifted (sig : Signature) where
  main : Tree.Def sig
  helpers : Array ElaboratedDef

private abbrev M := StateM (Nat × Array ElaboratedDef)

private abbrev RecEnv := ∀ {sig : Signature},
  Local sig → Args Expr sig.args → Prim sig.grade sig.result

private def bindRec {sig : Signature} {types : List ObjTy} (env : RecEnv)
    (name : Local sig) (ref : DeclRef { sig with args := sig.args ++ types })
    (captures : Args Expr types) : RecEnv :=
  fun {requested} key args =>
    if h : requested = sig then
      if h ▸ key = name then
        h.symm ▸ Prim.call (sig := { sig with args := sig.args ++ types }) ref
          ((h ▸ args).append captures)
      else env key args
    else env key args

mutual
  private def tree {types : List ObjTy} {g : Grade} {a : ObjTy}
      (owner : Lean.Name) (recs : RecEnv) (locals : Args Local types) :
      TreeRep g a → M (TreeRep g a)
    | .fail => pure .fail
    | .catching body handler => .catching <$> tree owner recs locals body <*> tree owner recs locals handler
    | .ret value => pure (.ret value)
    | .perform (.recur name args) => pure (.perform (recs name args))
    | .perform op => pure (.perform op)
    | .weaken included body => .weaken included <$> tree owner recs locals body
    | .block target body => .block target <$> tree owner recs locals body
    | .leave target value => pure (.leave target value)
    | .bind name value body => do
        let value ← tree owner recs locals value
        let body ← tree owner recs (.cons name locals) body
        pure (.bind name value body)
    | .branch condition yes no =>
        .branch condition <$> tree owner recs locals yes <*> tree owner recs locals no
    | .matchMany values arms => .matchMany values <$> rows owner recs locals arms
    | .scoped (g := bodyGrade) scope body => do
        let (index, helpers) ← get
        let name := Lean.Name.num owner index
        set (index + 1, helpers)
        let body ← tree owner recs locals body
        let signature : Signature := ⟨types, .i32, bodyGrade⟩
        let definition : Tree.Def signature := ⟨locals, ⟨body⟩⟩
        modify fun (index, helpers) => (index, helpers.push ⟨name, signature, definition⟩)
        pure (.perform (.execute scope (.named name) (locals.map Expr.local)))
    | .fix (sig := sig) key params body args => do
        let (index, helpers) ← get
        let name := Lean.Name.num owner index
        set (index + 1, helpers)
        let captures := locals.map Expr.local
        let signature := { sig with args := sig.args ++ types }
        let ref : DeclRef signature := .named name
        let body ← tree owner (bindRec recs key ref captures) (params.append locals) body
        let definition : Tree.Def signature := ⟨params.append locals, ⟨body⟩⟩
        modify fun (index, helpers) => (index, helpers.push ⟨name, signature, definition⟩)
        pure (.perform (.call (sig := signature) ref (args.append captures)))

  private def row {types patterns : List ObjTy} {result : ObjTy} {g : Grade}
      (owner : Lean.Name) (recs : RecEnv) (locals : Args Local types) :
      RowRep patterns result g → M (RowRep patterns result g)
    | .mk patterns names body =>
        .mk patterns names <$> tree owner recs (names.append locals) body

  private def rows {types patterns : List ObjTy} {result : ObjTy} {grades : List Grade}
      (owner : Lean.Name) (recs : RecEnv) (locals : Args Local types) :
      RowsRep patterns result grades → M (RowsRep patterns result grades)
    | .nil => pure .nil
    | .cons head tail => .cons <$> row owner recs locals head <*> rows owner recs locals tail
end

/-- Lift scoped and recursive bodies with their lexical telescopes before dependency collection. -/
public def lower {sig : Signature} (owner : Lean.Name) (source : Tree.Def sig) : Lifted sig :=
  let (body, (_, helpers)) := (tree owner Prim.recur source.params source.body.rep).run (0, #[])
  ⟨⟨source.params, ⟨body⟩⟩, helpers⟩

end Oria.Lower.Scope
