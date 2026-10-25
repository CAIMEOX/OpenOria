module

public import Oria.NumberProvider

namespace Oria.Examples.NumberProviderLogarithm

/-!
<https://arxiv.org/abs/2603.21852>
-/

/--
A fixed `[2/2]` rational approximation of `ln z` for `z ∈ [1/2, 2]`.

The definition is polymorphic over ordinary numeric syntax: Lean can evaluate it as `Float32`,
while `NumberProvider.F32` reifies the same source into a finite DP121 provider circuit.
-/
public def core {a : Type}
    [OfScientific a] [Neg a] [Add a] [Sub a] [Mul a] [Div a]
    (z : a) : a :=
  let t := (z - 1.0) / (z + 1.0)
  let u := t * t
  let p := 1.0 + u * (-(7.0 / 9.0) + u * (64.0 / 945.0))
  let q := 1.0 + u * (-(10.0 / 9.0) + u * (5.0 / 21.0))
  2.0 * t * p / q

/--
A finite approximation of `ln x` for positive, finite Float32 values.

Taking the 256th root places every positive finite Float32 in the approximation interval.
-/
public def ln {a : Type}
    [OfScientific a] [Neg a] [Add a] [Sub a] [Mul a] [Div a] [HPow a a a]
    (x : a) : a :=
  256.0 * core (x ^ (1.0 / 256.0 : a))

end Oria.Examples.NumberProviderLogarithm
