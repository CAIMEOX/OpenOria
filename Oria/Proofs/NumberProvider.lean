module

import Oria.NumberProvider
import Oria.Datapack.Version
meta import Lean.Elab.GuardMsgs
meta import Oria.NumberProvider

namespace Oria.Proofs.NumberProvider

open Oria
open Oria.NumberProvider

example : NumberProvider.version = Datapack.Version.dp121 := rfl

example : Datapack.Version.dataPackVersion NumberProvider.version = (121, 0) := rfl

private def score : Ref .int :=
  .named (.ofString "example:score")

private def multiplier : Ref .float :=
  .named (.ofString "example:multiplier")

private def rolls : Number .int :=
  16_777_217 + 3 * score - 1

private def speed : Number .float :=
  1.5 + multiplier / 2.0

private def scoreRange : NumberRange .int :=
  NumberRange.between score 20

#guard (ResourceId.parse "example:path/to_provider").isOk

#guard
  match ResourceId.parse "#example:not_a_holder" with
  | .error _ => true
  | .ok _ => false

#guard
  match ResourceId.parse "Example:uppercase" with
  | .error _ => true
  | .ok _ => false

example : Number .int := rolls
example : Number .float := speed

example : Number .int :=
  Number.binomial rolls 0.25

example : Number .float :=
  Number.fromInt rolls

example : Number .int :=
  Number.fromFloat speed

example : Number .int :=
  Number.abs (-rolls % 3) ^ 2

example : Number .int :=
  Number.floorDiv rolls 2 + Number.floorMod rolls 2

example : Number .int :=
  Number.average 1 [2, 3, 4]

example : Number .int :=
  min rolls 10

example : Number .float :=
  max speed 3.0

example : Number .int :=
  Number.uniform 1 6

example : Number .float :=
  Number.sqrt (Number.sin speed * Number.cos speed)

example : Number .float :=
  Number.ceil speed + Number.floor speed + Number.round speed + Number.truncate speed

example : Number .float :=
  Number.length 3 [4]

example : NumberRange .int := scoreRange

example : NumberRange .float :=
  NumberRange.exact speed

example : NumberRange .int :=
  NumberRange.atLeast score

example : NumberRange .float :=
  NumberRange.atMost speed

example : NumberRange .int :=
  NumberRange.any

#guard
  match NumberRange.toJson (NumberRange.exact (score : Number .int)) with
  | .ok encoded => encoded.compress == "\"example:score\""
  | .error _ => false

#guard
  match NumberRange.toJson scoreRange with
  | .ok encoded => encoded.compress == "{\"max\":20,\"min\":\"example:score\"}"
  | .error _ => false

#guard
  match NumberRange.toJson (NumberRange.atLeast (score : Number .int)) with
  | .ok encoded => encoded.compress == "{\"min\":\"example:score\"}"
  | .error _ => false

#guard NumberRange.references scoreRange == {
  ints := [score]
  floats := []
}

#guard
  match Number.toJson ((16_777_217 : Number .int) + 2) with
  | .ok encoded => encoded.compress ==
      "{\"inputs\":[16777217,2],\"type\":\"minecraft:add\"}"
  | .error _ => false

#guard
  match Number.toJson ((2 : Number .int) - 3) with
  | .ok encoded => encoded.compress ==
      "{\"left\":2,\"right\":3,\"type\":\"minecraft:sub\"}"
  | .error _ => false

#guard
  match Number.toJson ((2 : Number .int) ^ 3) with
  | .ok encoded => encoded.compress ==
      "{\"base\":2,\"exponent\":3,\"type\":\"minecraft:pow\"}"
  | .error _ => false

#guard
  match Number.toJson ((2.0 : Number .float) ^ (3.0 : Number .float)) with
  | .ok encoded => encoded.compress ==
      "{\"base\":2,\"exponent\":3,\"type\":\"minecraft:pow\"}"
  | .error _ => false

#guard
  match Number.toJson (-(2 : Number .int)) with
  | .ok encoded => encoded.compress ==
      "{\"input\":2,\"type\":\"minecraft:negate\"}"
  | .error _ => false

#guard
  match Number.toJson (Number.binomial 3 0.5) with
  | .ok encoded => encoded.compress ==
      "{\"n\":3,\"p\":0.5,\"type\":\"minecraft:binomial\"}"
  | .error _ => false

#guard
  match Number.toJson (Number.fromInt 3) with
  | .ok encoded => encoded.compress ==
      "{\"input\":3,\"type\":\"minecraft:from_int\"}"
  | .error _ => false

#guard
  match Number.toJson (Number.uniform (1 : Number .float) 6) with
  | .ok encoded => encoded.compress ==
      "{\"max\":6,\"min\":1,\"type\":\"minecraft:uniform\"}"
  | .error _ => false

#guard
  match Number.renderSnbt ((2 : Number .int) + 3) 120 with
  | .ok encoded => encoded == "{\"type\":\"minecraft:add\",\"inputs\":[2,3]}"
  | .error _ => false

#guard
  match Number.renderSnbt ((2 : Number .float) + 3) 120 with
  | .ok encoded => encoded == "{\"type\":\"minecraft:add\",\"inputs\":[2f,3f]}"
  | .error _ => false

#guard (Number.toNbt ((2 : Number .int) + 3)).toOption.any (fun value => value.1 == .compound)

#guard Number.references (Number.binomial score multiplier : Number .int) == {
  ints := [score]
  floats := [multiplier]
}

#guard
  match Number.toJson (Number.intConstant 2_147_483_648) with
  | .error (.intConstantOutOfRange 2_147_483_648) => true
  | _ => false

#guard
  match Number.toJson (-2_147_483_648 : Number .int) with
  | .ok encoded => encoded.compress == "-2147483648"
  | .error _ => false

#guard
  match Number.toJson <| Number.floatConstant ((1 : Float32) / 0) with
  | .error (.nonFiniteFloatConstant "Infinity") => true
  | _ => false

#guard
  match Number.toJson ((1 + 2 : Number .int) + 3),
      Number.toJson (Number.add (1 : Number .int) [2, 3]) with
  | .ok nested, .ok flat => nested.compress != flat.compress
  | _, _ => false

end Oria.Proofs.NumberProvider
