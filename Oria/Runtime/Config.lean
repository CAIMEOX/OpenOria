module

public import Oria.Datapack.Resource
public import Oria.Command.Argument

namespace Oria.Runtime

/-- Identities shared by generated runtime code and the physical memory operations. -/
public structure Config where
  ns : Datapack.ResourceNamespace
  storage : ResourceId
  runtime : ResourceId
  objective : Command.Objective

end Oria.Runtime
