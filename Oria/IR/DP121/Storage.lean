module

public import Oria.Nbt.Basic
public import Oria.Datapack.ResourceId

namespace Oria.Target.DP121

/-- A Minecraft command-storage resource and a path within its NBT contents. -/
public structure StoragePath where
  storage : Oria.ResourceId
  path : Nbt.Path
  deriving BEq, DecidableEq, Repr

end Oria.Target.DP121
