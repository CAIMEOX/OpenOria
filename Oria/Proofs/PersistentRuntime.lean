module

import Oria.Compiler.Lower.DP121.Persistent.Runtime
import Oria.IR.DP121.Pretty
meta import Oria.Compiler.Lower.DP121.Persistent.Runtime
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.PersistentRuntime

open Oria Oria.Command Oria.Datapack Oria.Target.DP121 Nbt

private def config : Oria.Runtime.Config := {
  ns := ResourceNamespace.ofString "test"
  storage := ResourceId.ofString "test:persistent"
  runtime := ResourceId.ofString "test:runtime"
  objective := Objective.ofString "test"
}

private def hasFunction
    (suffix : String)
    (result : Except Diagnostic (List ((kind : FunctionKind) × FunctionDef kind))) : Bool :=
  match result with
  | .error _ => false
  | .ok functions => functions.any fun function =>
      match function with
      | ⟨_, definition⟩ =>
          definition.ref.id.path.render == "__oria/persistent/" ++ suffix

private def hasBodyText
    (suffix text : String)
    (result : Except Diagnostic (List ((kind : FunctionKind) × FunctionDef kind))) : Bool :=
  match result with
  | .error _ => false
  | .ok functions => functions.any fun function =>
      let definition := function.2
      definition.ref.id.path.render == "__oria/persistent/" ++ suffix &&
        (definition.body.pretty 120).contains text

private def hasNoBodyText
    (suffix text : String)
    (result : Except Diagnostic (List ((kind : FunctionKind) × FunctionDef kind))) : Bool :=
  !hasBodyText suffix text result

private def generatedCallsClosed : Bool :=
  match Lower.DP121.Persistent.Runtime.generate config with
  | .error _ => false
  | .ok functions =>
      let functions := functions.toArray
      if unique : (functions.toList.map fun function => function.2.ref.id.render).Nodup then
        (Target.DP121.Program.of functions unique).checkCalls.isOk
      else
        false

#guard (Lower.DP121.Persistent.Runtime.ref config "allocate").isOk
#guard (Lower.DP121.Persistent.Runtime.source config).path == some (Nbt.Path.key "memory_arg")
#guard (Lower.DP121.Persistent.Runtime.address config (.inl 3)).length == 1
#guard (Lower.DP121.Persistent.Runtime.address config (.inl 3)).head?.map
    (Command.pretty · 120) =
      some "data modify storage test:runtime \"memory_arg\".\"p0\" set value 2"
#guard (Lower.DP121.Persistent.Runtime.address config
    (.inr (Lower.DP121.Persistent.Runtime.score config (.ofString "#p_result")))).length == 3
#guard hasFunction "allocate" (Lower.DP121.Persistent.Runtime.generate config)
#guard hasFunction "replace" (Lower.DP121.Persistent.Runtime.generate config)
#guard hasFunction "read" (Lower.DP121.Persistent.Runtime.generate config)
#guard hasFunction "next" (Lower.DP121.Persistent.Runtime.generate config)
#guard hasFunction "stamp" (Lower.DP121.Persistent.Runtime.generate config)
#guard hasBodyText "allocate/free" "#p_result"
    (Lower.DP121.Persistent.Runtime.generate config)
#guard hasNoBodyText "allocate/free" "run function test:__oria/persistent/read"
    (Lower.DP121.Persistent.Runtime.generate config)
#guard hasNoBodyText "allocate/free" "run function test:__oria/persistent/replace"
    (Lower.DP121.Persistent.Runtime.generate config)
#guard hasNoBodyText "allocate/free" "run function test:__oria/persistent/next"
    (Lower.DP121.Persistent.Runtime.generate config)
#guard hasBodyText "allocate/append" "2147483647"
    (Lower.DP121.Persistent.Runtime.generate config)
#guard hasNoBodyText "allocate" "players set #panic test 0"
    (Lower.DP121.Persistent.Runtime.generate config)

#guard generatedCallsClosed

end Oria.Proofs.PersistentRuntime
