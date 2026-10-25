module

import Oria.Datapack.Artifact
import Lean.Meta.Eval

namespace Oria.Datapack.Eval

/-- Typed evaluator for the inert, already checked pack specification. -/
private unsafe def specImpl (value : Lean.Expr) : Lean.MetaM Spec :=
  Lean.Meta.evalExpr Spec (Lean.mkConst ``Spec) value (checkMeta := false)

@[implemented_by specImpl]
opaque spec (value : Lean.Expr) : Lean.MetaM Spec

/-- Typed evaluator for the rendered files published by a checked pack declaration. -/
private unsafe def artifactImpl (value : Lean.Expr) : Lean.MetaM Artifact :=
  Lean.Meta.evalExpr Artifact (Lean.mkConst ``Artifact) value (checkMeta := false)

@[implemented_by artifactImpl]
opaque artifact (value : Lean.Expr) : Lean.MetaM Artifact

end Oria.Datapack.Eval
