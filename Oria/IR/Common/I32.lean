module

namespace Oria.I32

/--
Native scoreboard division rounds toward negative infinity, fails for a zero divisor,
and wraps the signed overflow case `MIN / -1` to `MIN`.
-/
@[expose] public def divide (left right : Int32) : Option Int32 :=
  if right = 0 then none
  else
    let quotient := left / right
    let remainder := left % right
    some (if remainder ≠ 0 ∧ ((left < 0) ≠ (right < 0)) then quotient - 1 else quotient)

@[simp] public theorem divide_zero (value : Int32) : divide value 0 = none := by
  simp [divide]

/-- A zero divisor is the sole native arithmetic failure. -/
public theorem divide_eq_none (left right : Int32) : divide left right = none ↔ right = 0 := by
  simp [divide]

@[simp] public theorem divide_one (value : Int32) : divide value 1 = some value := by
  simp [divide]

end Oria.I32
