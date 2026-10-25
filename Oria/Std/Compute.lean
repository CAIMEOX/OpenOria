module

public import Oria.Std.Command.Arg.Data
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Number provider evaluation

`Compute.run` evaluates an integer or float provider; `scaled` scales a float result.
Command payloads are I32, with float results rounded down. To retain a FloatTag, use a
compute source with Data.modify. `Provider.named` references a loaded resource, while
`Provider.ofNbt` carries a host-constructed provider. Minecraft checks its schema and
evaluates it according to the provider's rules.

`Oria.NumberProvider` constructs compound expressions and retains their context dependencies.
Import `Oria.Std.Compute.Number` to preserve this summary in `Calculation.ofNumber`.
Constants and known arithmetic need only the native context-construction reads: position
and dimension. Named resources and arbitrary descriptions add the full context requirement.
The effect bound covers world access, score reads, and randomness for every provider.
-/

namespace Oria.Std.Compute

open Oria.Std.Command.Arg

/-- Combine native context-construction reads with the provider's dependency summary.
World, scoreboard-reading, and random effects remain a conservative bound. -/
@[expose] public def grade (context : ComputeContext) (extraReq : ReqRow := Req.none) : Grade :=
  ⟨context.requirements ||| extraReq, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/--
Evaluate a provider in the given context. Integer results become the success payload
directly; float results are rounded down to I32. Resource, context, or evaluation failures
produce a failed result. The native parser checks the construction-time description.

```lean
open Oria Oria.Std
example := Compute.run .default (.integer (.ofNbt (7 : Int32)))
```
-/
public def run (context : ComputeContext) (calculation : Calculation) :
    Prog (grade context calculation.requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, ComputeContext.requirements,
    Oria.Command.Call.grade, Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.compute, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.compute.call <|
      .cons (Oria.Command.encode context) <| .cons (Oria.Command.encode calculation) .nil)

/-- Evaluate a float provider, multiply by a finite construction-time Float32 scale, and
round down to an I32 payload. Failure conditions follow run. Use this to encode fractional
values as scaled integers. -/
public def scaled (context : ComputeContext) (provider : Provider) (scale : Float32) :
    Prog (grade context provider.requirements) Int32 := by
  simpa [Eff.failure, Grade.seq, Grade.failure, grade, ComputeContext.requirements,
    Oria.Command.Call.grade, Oria.Command.Call.requirements, Oria.Command.Ref.call,
    Command.Declarations.computeScaled, Req.none, BitVec.or_assoc] using
    (Oria.Command.emit <| Command.Declarations.computeScaled.call <|
      .cons (Oria.Command.encode context) <| .cons (Oria.Command.encode provider) <|
        .cons (Oria.Command.encode scale) .nil)

end Oria.Std.Compute
