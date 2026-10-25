module

public import Oria.IR.Tree.Definition

namespace Oria

open IR

/-- Immutable Tree artifact exchanged by the frontend, catalogues, and compiler passes. -/
public structure ElaboratedDef where
  private mk ::
  source : Lean.Name
  signature : Signature
  definition : IR.Tree.Def signature

/-- A root's logical type is the result type of its closed initializer. -/
public structure RootDefinition where
  initial : ElaboratedDef
  ref : IR.RootRef initial.signature.result

end Oria
