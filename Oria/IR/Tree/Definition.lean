module

public import Oria.IR.Tree.Build
import all Oria.IR.Tree.Build

namespace Oria.IR.Tree

/-- A complete structured definition indexed by its object-language signature. -/
public structure Def (sig : Signature) where
  private mk ::
  private params : Args Local sig.args
  private body : Tree sig.grade sig.result

namespace Def

/--
Construct a definition in one private fresh-name run. Public builders mint parameters and local
binders from this single supply, so ANF lowering can translate their nominal identities to typed
lexical positions while it traverses the Tree.
-/
public def build {sig : Signature}
    (body : Args Expr sig.args → Build (Tree sig.grade sig.result)) :
    Def sig :=
  let action := do
    let (params, expressions) ← Build.parameters sig.args
    let body ← body expressions
    pure (params, body)
  let ((params, body), _) := Build.runFrom 0 action
  ⟨params, body⟩

end Def

end Oria.IR.Tree
