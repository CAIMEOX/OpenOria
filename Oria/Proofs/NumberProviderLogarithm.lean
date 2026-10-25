module

import Oria.Examples.NumberProviderLogarithm
meta import Oria.Examples.NumberProviderLogarithm
meta import Oria.NumberProvider

namespace Oria.Proofs.NumberProviderLogarithm

open Oria
open Oria.NumberProvider

/- These are smoke tests, not a global error bound for every Float32 bit pattern. -/
private def closeAtSmokePoint (x : Float32) : Bool :=
  Float32.abs (Examples.NumberProviderLogarithm.ln x - Float32.log x) < 0.00001

#guard closeAtSmokePoint 0.001
#guard closeAtSmokePoint 0.5
#guard closeAtSmokePoint 1.0
#guard closeAtSmokePoint 2.0
#guard closeAtSmokePoint 1000.0

private def input : Ref .float :=
  .named (.ofString "oria_demo:input")

example : F32 :=
  Examples.NumberProviderLogarithm.ln (input : F32)

#eval IO.println $
  match (Number.toJson (Examples.NumberProviderLogarithm.ln (input : F32))) with
    | .ok encoded => encoded.pretty
    | .error _ => "error"

#guard
  match Number.toJson (Examples.NumberProviderLogarithm.ln (input : F32)) with
  | .ok encoded =>
      let text := encoded.compress
      let exactRatios := [
        "\"exponent\":{\"left\":1,\"right\":256,\"type\":\"minecraft:div\"}",
        "{\"left\":7,\"right\":9,\"type\":\"minecraft:div\"}",
        "{\"left\":64,\"right\":945,\"type\":\"minecraft:div\"}",
        "{\"left\":10,\"right\":9,\"type\":\"minecraft:div\"}",
        "{\"left\":5,\"right\":21,\"type\":\"minecraft:div\"}"
      ]
      text.contains "minecraft:pow" && exactRatios.all fun ratio => text.contains ratio
  | .error _ => false

end Oria.Proofs.NumberProviderLogarithm
