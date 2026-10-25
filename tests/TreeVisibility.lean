module

import Oria.Language.Builder

namespace Oria.Tests.TreeVisibility

open Oria Oria.IR Oria.IR.Tree

example (definition : ElaboratedDef) : Lean.Name :=
  definition.source

example (definition : ElaboratedDef) : Signature :=
  definition.signature

example (definition : ElaboratedDef) : Def definition.signature :=
  definition.definition

end Oria.Tests.TreeVisibility
