module

import Oria.Effect.Labels

namespace Oria.Proofs.TaskBudget

/-- Precharging an upper bound preserves the credit reserved for parking. -/
theorem charge_preserves_reserve {available fuel reserve charged actual : Nat}
    (space : fuel + reserve ≤ available) (admitted : charged ≤ fuel) (bound : actual ≤ charged) :
    fuel - charged + reserve ≤ available - actual := by omega

/-- The parking path fits even when no work credit remains. -/
theorem parking_fits {available fuel reserve parking : Nat}
    (space : fuel + reserve ≤ available) (bound : parking ≤ reserve) : parking ≤ available := by omega

/-- The slice starts with its bootstrap and parking costs accounted for. -/
theorem initial_reserve {budget bootstrap reserve : Nat} (fits : bootstrap + reserve ≤ budget) :
    budget - bootstrap - reserve + reserve ≤ budget - bootstrap := by omega

/-- Recovering from Failure leaves the suspension contract intact. -/
theorem recovery_preserves_suspension (g : Oria.Grade) : g.handled.canSuspend = g.canSuspend := by
  simp [Oria.Grade.handled, Oria.Grade.canSuspend, Oria.Grade.failure]

end Oria.Proofs.TaskBudget
