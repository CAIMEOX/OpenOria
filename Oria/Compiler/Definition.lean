module

public import Oria.Compiler.Lower.ANF
public import Oria.Compiler.Optimize.Cont
public import Oria.Compiler.Optimize.Memory

namespace Oria.Compiler

/-- Link one elaborated definition through every catalogue, then lower its Tree to Cont ANF. -/
public def compile
    (functions : Function.Catalog)
    (objects : ObjectCatalog)
    (commands : Command.Catalog)
    (definition : ElaboratedDef) :
    Except Diagnostic (IR.Cont.Def definition.signature) := do
  let objectLinked ← objects.link definition.definition
  let commandLinked ← commands.link objectLinked
  let functionLinked ← functions.link commandLinked
  (Optimize.Memory.run ∘ Optimize.Cont.run) <$> Lower.ANF.lower definition.source functionLinked

end Oria.Compiler
