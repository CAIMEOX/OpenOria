module

public import Oria.IR.Cont.Syntax

namespace Oria.IR.Cont

/-- A complete continuation definition indexed by its object-language signature. -/
public structure Def (sig : Signature) where
  private mk ::
  private body : Comp sig.args sig.result []

namespace Def

/-- Construct a definition from its intrinsic signature-indexed parameter telescope. -/
public def build {sig : Signature}
    (body : Args (Atom sig.args) sig.args →
      Comp sig.args sig.result []) :
    Def sig :=
  let parameters :=
    (Scope.Var.identity Unit sig.args).map Atom.local
  ⟨body parameters⟩

/-- Read-only projection of the definition's scoped computation. -/
@[expose] public def computation {sig : Signature} (definition : Def sig) :
    Comp sig.args sig.result [] :=
  private_decl% definition.body

/-- Observing a built definition yields its callback applied to the identity telescope. -/
@[simp] public theorem computation_build
    {sig : Signature}
    (body : Args (Atom sig.args) sig.args →
      Comp sig.args sig.result []) :
    computation (build body) =
      body ((Scope.Var.identity Unit sig.args).map Atom.local) := by
  rfl

end Def

end Oria.IR.Cont
