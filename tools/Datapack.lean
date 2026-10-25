module

import Oria.Datapack.Export
import Lean.Util.Path

public def main (args : List String) : IO UInt32 := do
  let [moduleName, destination] := args
    | throw (.userError "usage: oria-export <module> <managed-output-directory>")
  Lean.initSearchPath (← Lean.findSysroot)
  Oria.Datapack.exportModule moduleName.toName destination
  return 0
