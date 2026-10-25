module

public import Oria.Compiler.Lower.DP121.Stack
public import Oria.Compiler.Lower.DP121.Persistent.Runtime
public import Oria.Datapack.Spec

namespace Oria.Lower.DP121

open Oria.Datapack Oria.Target.DP121

public abbrev PackedFunction := (kind : FunctionKind) × FunctionDef kind

public structure Emitted where
  commands : List (Command .plain)
  helpers : List PackedFunction := []

public structure Config where
  resourceNamespace : ResourceNamespace
  objective : Oria.Command.Objective
  rootNames : Std.HashMap Lean.Name ResourceId := {}
  collectors : Array ((g : Grade) × PublicFunctionPath × IR.DeclRef ⟨[], .unit, g⟩) := #[]
  globals : Array IR.Nbt.GlobalDecl := #[]
  /-- Pack-owned data keeps its namespace when task code uses a separate workspace. -/
  dataNamespace : ResourceNamespace := resourceNamespace
  registerBudget : Nat := 128
  sliceBudget : Nat := 20000

public def Config.function (config : Config) (path : String) :
    Except Diagnostic (FunctionRef .plain) := do
  let path ← (ResourcePath.parse path).mapError fun | .invalidResourceId value => .invalidResourceId value
  pure (.ofId (.ofParts config.resourceNamespace path))

public def Config.runtime (config : Config) : Except Diagnostic ResourceId :=
  (ResourceId.parse (config.resourceNamespace.render ++ ":runtime")).mapError
    fun | .invalidResourceId value => .invalidResourceId value

public def Config.memory (config : Config) : Except Diagnostic Oria.Runtime.Config := do
  let storage ← (ResourceId.parse (config.dataNamespace.render ++ ":persistent")).mapError (fun
    | .invalidResourceId value => .invalidResourceId value)
  pure ⟨config.resourceNamespace, storage, ← config.runtime, config.objective⟩

/-- Qualify a native global using its owning pack, independently of function placement. -/
public def Config.global (config : Config) (ref : IR.Nbt.GlobalRef) : Except Diagnostic StoragePath := do
  let storage ← (ResourceId.parse (config.dataNamespace.render ++ ":" ++ ref.storage.render)).mapError
    (fun | .invalidResourceId value => .invalidResourceId value)
  pure ⟨storage, ref.path⟩

end Oria.Lower.DP121
