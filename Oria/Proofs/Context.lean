module

import Oria.Effect.Context
import Oria.Effect.Labels

namespace Oria.Proofs.Context

open Oria

private def asAllPlayers : ContextChange :=
  ⟨Req.none, Req.executor⟩

private def atSelf : ContextChange :=
  ⟨Req.executor, Req.position ||| Req.rotation⟩

private def executorPositionRotation : ReqRow :=
  Req.executor ||| Req.position ||| Req.rotation

/- The conventional labels are E = 1, P = 2, and R = 4. -/
example : Req.executor = 1#8 := rfl
example : Req.position = 2#8 := rfl
example : Req.rotation = 4#8 := rfl

example :
    ContextChange.apply
      (ContextChange.seq asAllPlayers atSelf) Req.none = Req.none := by
  rfl

example :
    ContextChange.apply
      (ContextChange.seq atSelf asAllPlayers) Req.none = Req.executor := by
  rfl

example :
    (ContextChange.seq asAllPlayers atSelf).give = executorPositionRotation := by
  rfl

example :
    (ContextChange.seq atSelf asAllPlayers).need = Req.executor := by
  rfl

end Oria.Proofs.Context
