module

import Oria.Nbt
meta import Lean.Elab.Command

open Lean Lean.Elab.Command in
run_cmd do
  for imported in (← getEnv).header.moduleNames do
    if (`Oria).isPrefixOf imported && !(`Oria.Nbt).isPrefixOf imported &&
        imported != `Oria.Data.Sealed then
      throwError "Oria.Nbt imports an unrelated Oria module: {imported}"

open Oria

private structure Message where
  text : String
  count : Int32
  deriving Nbt.ToNbt, Nbt.FromNbt

example (message : Message) : Nbt.Value .compound := nbt% {message: $(message)}
