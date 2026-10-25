module

public import Oria.IR.Tree.Syntax
import all Oria.IR.Common.Local
import all Oria.IR.Tree.Syntax

namespace Oria.IR.Tree

/-- Private fresh-name computation used while constructing one Tree definition. -/
public structure Build (A : Type) where
  private mk ::
  private runState : StateM Nat A

namespace Build

private def make {A : Type} (runState : StateM Nat A) : Build A :=
  ⟨runState⟩

public instance : Monad Build :=
  private_decl% {
    pure := fun value => make (pure value)
    bind := fun action next => make do
      let value ← action.runState
      (next value).runState
  }

private def fresh {α : Type} (a : α) : Build (Local a) :=
  make do
    let serial ← get
    set (serial + 1)
    pure (Local.fresh serial)

private def freshArgs : (types : List ObjTy) → Build (Args Local types)
  | [] => pure .nil
  | ty :: types => do
      let name ← fresh ty
      let rest ← freshArgs types
      pure (.cons name rest)

/-- Introduce one fresh lexical return destination while quoting a structured block. -/
public def block {g : Grade} {a : ObjTy}
    (body : Local a → Build (Tree g a)) : Build (Tree g a) :=
  private_decl% (do
    let target ← fresh a
    let body ← body target
    pure ⟨.block target body.rep⟩)

/-- Introduce one lexical result local and build its body under that local. -/
public def bind
    {g₁ : Grade} {a : ObjTy} {g₂ : Grade} {b : ObjTy}
    (value : Tree g₁ a)
    (body : Expr a → Build (Tree g₂ b)) :
    Build (Tree (g₁.seq g₂) b) :=
  private_decl% (do
    let name ← fresh a
    let body ← body (.local name)
    pure (Tree.bindLocal name value body))

/-- Quote one recursive function body; recursive uses emit symbolic local calls. -/
public def fix {sig : Signature}
    (body : (Args Expr sig.args → Tree sig.grade sig.result) →
      Args Expr sig.args → Build (Tree sig.grade sig.result))
    (arguments : Args Expr sig.args) : Build (Tree sig.grade sig.result) :=
  private_decl% (do
    let name ← fresh sig
    let params ← freshArgs sig.args
    let body ← body (fun args => Tree.perform (.recur name args)) (params.map Expr.local)
    pure ⟨.fix name params body.rep arguments⟩)

/-- Bind a unary constructor's payload in its matching alternative. -/
public def caseUnary
    {t : ObjTy} {a : ObjTy} {gn : Grade} {b : ObjTy} {gs : Grade}
    (empty : Constructor t []) (full : Constructor t [a])
    (scrutinee : Expr t)
    (noneBody : Tree gn b)
    (someBody : Expr a → Build (Tree gs b)) :
    Build (Tree (gn.join gs) b) :=
  private_decl% (do
    let name ← fresh a
    let someBody ← someBody (.local name)
    pure ⟨.matchMany (.cons scrutinee .nil)
      (.cons (.mk (.cons (.ctor empty .nil) .nil) .nil noneBody.rep)
        (.cons (.mk (.cons (.ctor full (.cons .bind .nil)) .nil)
          (.cons name .nil) someBody.rep) .nil))⟩)

/-- Bind every pattern variable once while quoting its source row. -/
public def row {types : List ObjTy} {bindings : List ObjTy} {g : Grade} {result : ObjTy}
    (patterns : Patterns types bindings)
    (body : Args Expr bindings → Build (Tree g result)) : Build (Row types result g) :=
  private_decl% (do
    let locals ← freshArgs bindings
    let body ← body (locals.map Expr.local)
    pure ⟨.mk patterns locals body.rep⟩)

public def noRows {types : List ObjTy} {result : ObjTy} : Build (Rows types result []) :=
  private_decl% pure ⟨.nil⟩

public def consRow {types : List ObjTy} {result : ObjTy} {g : Grade} {gs : List Grade}
    (row : Build (Row types result g))
    (rest : Build (Rows types result gs)) : Build (Rows types result (g :: gs)) :=
  private_decl% (do
    let row ← row
    let rest ← rest
    pure ⟨.cons row.rep rest.rep⟩)

/-- Mint a typed parameter telescope and the expressions visible to the source builder. -/
private def parameters (types : List ObjTy) : Build (Args Local types × Args Expr types) := do
  let locals ← freshArgs types
  pure (locals, locals.map Expr.local)

/-- Trusted definition construction runs the otherwise opaque fresh-name computation. -/
private def runFrom {A : Type} (next : Nat) (action : Build A) : A × Nat :=
  action.runState next

end Build

end Oria.IR.Tree
