module

public import Oria.IR.Cont.Syntax

namespace Oria.IR.Cont

/-- A simultaneous type-preserving substitution, including propagated scalar literals. -/
public abbrev Subst (Γ Δ : List ObjTy) := Args (Atom Δ) Γ

namespace Subst

@[expose] public def identity (Γ : List ObjTy) : Subst Γ Γ :=
  (Scope.Var.identity Unit Γ).map Atom.local

@[expose] public def atom {Γ Δ : List ObjTy} {a : ObjTy} (σ : Subst Γ Δ) : Atom Γ a → Atom Δ a
  | .local x => x.lookup σ
  | .unit => .unit
  | .bool x => .bool x
  | .i32 x => .i32 x

@[expose] public def lift {Γ Δ : List ObjTy} (σ : Subst Γ Δ) (as : List ObjTy) :
    Subst (as ++ Γ) (as ++ Δ) :=
  ((Scope.Var.identity Unit as).map fun x =>
    Atom.local (Scope.Renaming.appendLeft Unit as Δ x)).append
      (σ.map fun x => x.weakenMany as)

end Subst
end Oria.IR.Cont
