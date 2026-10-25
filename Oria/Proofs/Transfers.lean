module

import Oria.Compiler.Lower.DP121.Transfer
meta import Oria.Compiler.Lower.DP121.Transfer

namespace Oria.Proofs.Transfers

open Oria.Lower.DP121.Transfer

private def swap : List (Move (Fin 4)) := [⟨0, .loc 1⟩, ⟨1, .loc 0⟩]
private def cycle : List (Move (Fin 4)) := [⟨0, .loc 1⟩, ⟨1, .loc 2⟩, ⟨2, .loc 0⟩]

#guard (schedule (3 : Fin 4) swap).isSome
#guard (schedule (3 : Fin 4) cycle).isSome

private def code := (schedule (3 : Fin 4) swap).get (by native_decide)

example (state : Fin 4 → Int32) (i : Fin 4) (outside : i ≠ 3) :
    run state code.code i = simultaneous state swap i :=
  code.correct state i outside

private def wide : List (Move Nat) :=
  (List.range 64).map fun i => ⟨i, .loc (i + 100)⟩

#guard (schedule 1000 wide).isSome

private def wideCode := (schedule 1000 wide).get (by native_decide)

example (state : Nat → Int32) (i : Nat) (outside : i ≠ 1000) :
    run state wideCode.code i = simultaneous state wide i :=
  wideCode.correct state i outside

end Oria.Proofs.Transfers
