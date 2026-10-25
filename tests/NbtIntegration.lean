module

public import Oria.Nbt
public import Oria
import Oria.NumberProvider
meta import Oria.Nbt
meta import Oria
meta import Oria.NumberProvider

public structure Stats where
  points : Int32
  active : Bool
  deriving Oria.Object, Oria.Nbt.ToNbt, Oria.Nbt.FromNbt

#guard (Oria.Nbt.ToNbt.toNbt (Stats.mk 12 true)).2.renderSnbt.toOption =
  some "{\"points\":12,\"active\":1b}"
#guard (Oria.Nbt.FromNbt.fromNbt (a := Stats) ⟨_, nbt% {points: 12, active: true}⟩).toOption.map (·.points) =
  some 12

private def provider : Except Oria.NumberProvider.Error (Oria.Nbt.Value .compound) := do
  let value ← (2 + 3 : Oria.NumberProvider.I32).toNbt
  pure (nbt% {amount: $(value)})

#guard provider.toOption.bind (fun v => v.renderSnbt.toOption) =
  some "{\"amount\":{\"type\":\"minecraft:add\",\"inputs\":[2,3]}}"
