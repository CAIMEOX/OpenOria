module

public import Oria.Std.Command.Arg.World
import Oria.Std.Command.Declarations.World
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Weather

Weather changes apply to server weather state. Omitted durations use the source dimension's random
generator. Explicit durations use native time units. Commands return native results: -1 for a
sampled duration, or the requested tick count.
-/

namespace Oria.Std.Weather

open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Sampled durations read the source dimension and random state; explicit durations require neither. -/
@[expose] public def grade (duration : Option Oria.Std.Command.Arg.Time := none) : Grade :=
  ⟨if duration.isNone then Req.dimension else Req.none,
    (if duration.isNone then Eff.world ||| Eff.random else Eff.world) ||| Eff.failure⟩

/-- Set weather. Explicit durations require at least one tick after native rounding.
Static invalid arguments can prevent loading; dynamic invalid arguments fail on invocation. -/
public def set (mode : WeatherKind) (duration : Option Oria.Std.Command.Arg.Time := none) :
    Prog (grade duration) Int32 :=
  match duration with
  | none => do
      emit <| Command.Declarations.weather.call <| .cons (encode mode) <| .nil
  | some t => do
      emit <| Command.Declarations.weatherFor.call <| .cons (encode mode) <| .cons (encode t) <| .nil

end Oria.Std.Weather
