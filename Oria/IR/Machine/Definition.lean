module

public import Oria.IR.Machine.Syntax
public import Oria.Data.IndexedVector

namespace Oria.IR.Machine

/-- A finite CFG with a body at every predeclared, arity-indexed block position. -/
public structure Def (functions : List Signature) (sig : Signature) where
  layout : List Nat
  entry : Scope.Var Unit layout sig.args
  blocks : Data.IndexedVector fun i : Fin layout.length =>
    Body functions layout sig.result (layout.get i)

namespace Def

public def block {functions : List Signature} {sig : Signature} {n : Nat}
    (definition : Def functions sig) (ref : Scope.Var Unit definition.layout n) :
    Body functions definition.layout sig.result n :=
  ref.typeCorrect ▸ definition.blocks.get ref.index

end Def
end Oria.IR.Machine
