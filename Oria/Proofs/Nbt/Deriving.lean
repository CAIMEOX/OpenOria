module

public import Oria.Proofs.Nbt.Support
meta import Oria.Proofs.Nbt.Support

namespace Oria.Proofs.Nbt

open Oria.Nbt

public structure Player where
  name : String
  points : Int32
  active : Bool
  deriving BEq, @[expose] Oria.Nbt.ToNbt, @[expose] Oria.Nbt.FromNbt

public inductive Choice where
  | rock | paper | scissors
  deriving BEq, @[expose] Oria.Nbt.ToNbt, @[expose] Oria.Nbt.FromNbt

public inductive State where
  | idle
  | playing (player computer : Int32)
  deriving BEq, @[expose] Oria.Nbt.ToNbt, @[expose] Oria.Nbt.FromNbt

public structure Box (a : Type u) where
  value : a
  label : String
  deriving @[expose] Oria.Nbt.ToNbt, @[expose] Oria.Nbt.FromNbt

public inductive Envelope (a : Type u) where
  | empty
  | item (value : a) (label : String)
  deriving @[expose] Oria.Nbt.ToNbt, @[expose] Oria.Nbt.FromNbt

#guard (ToNbt.toNbt (Player.mk "Alex" 12 true)).2.renderSnbt.toOption =
  some "{\"name\":\"Alex\",\"points\":12,\"active\":1b}"
#guard FromNbt.fromNbt (a := Player) ⟨_, nbt% {active: true, points: 12, name: "Alex", extra: 0}⟩ ==
  .ok ⟨"Alex", 12, true⟩
#guard FromNbt.fromNbt (a := Player) ⟨_, nbt% {name: "Alex", points: 1, active: false, points: 2}⟩ ==
  .ok ⟨"Alex", 2, false⟩
#guard FromNbt.fromNbt (a := Player) ⟨_, nbt% {name: "Alex", active: false}⟩ ==
  .error ⟨[.key ⟨"points"⟩], .missingField⟩
#guard FromNbt.fromNbt (a := List Player) ⟨_, nbt% [{name: "Alex", points: 1L, active: true}]⟩ ==
  .error ⟨[.index 0, .key ⟨"points"⟩], .tag .int .long⟩
#guard (ToNbt.toNbt Choice.rock).2.renderSnbt.toOption = some "\"rock\""
#guard FromNbt.fromNbt (a := Choice) ⟨_, nbt% "paper"⟩ == .ok .paper
#guard (ToNbt.toNbt State.idle).2.renderSnbt.toOption = some "{\"idle\":[]}"
#guard (ToNbt.toNbt (State.playing 1 2)).2.renderSnbt.toOption = some "{\"playing\":[1,2]}"
#guard FromNbt.fromNbt (a := State) ⟨_, nbt% {playing: [1, 2]}⟩ == .ok (.playing 1 2)
#guard FromNbt.fromNbt (a := State) ⟨_, nbt% {playing: [1]}⟩ ==
  .error ⟨[.key ⟨"playing"⟩], .arity 2 1⟩
#guard FromNbt.fromNbt (a := State) ⟨_, nbt% {idle: [], playing: [1, 2]}⟩ ==
  .error ⟨[], .constructorKeys 2⟩

end Oria.Proofs.Nbt
