module

public import Oria.Std.Command.Arg.Registry
import Oria.Std.Command.Declarations.Utility
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Location queries

Locate searches from the execution position in the execution dimension. Native results are
integer distances; coordinates are emitted as operator feedback. Search policies differ:
structure and POI report horizontal distance, while biome reports three-dimensional distance.
Minecraft floors these distances after its native floating-point calculation.

Resource IDs and tags are construction-time values. Structure and biome search can be
expensive; callers control when queries run. A missing result is a command failure.
-/

namespace Oria.Std.Locate
open Oria.Command (ResourceOrTag encode emit)

/-- Native searches read position and dimension and carry the world effect. -/
@[expose] public def grade : Grade :=
  ⟨Req.position ||| Req.dimension, Eff.world ||| Eff.failure⟩

/-- Locate a registered structure or tag. Returns floored horizontal distance; native
feedback contains coordinates. Uses the generator's placement policy with a native search
bound of 100; random-spread search extent depends on placement spacing.
An invalid resource or absent structure fails. -/
public def «structure» (target : ResourceOrTag) : Prog grade Int32 := do
  emit <| Command.Declarations.locateStructure.call <| .cons (encode target) .nil

/-- Locate a biome ID or tag. Returns floored three-dimensional distance. The native search
uses a 6400-block radius with horizontal/vertical sample steps of 32/64 blocks. -/
public def biome (target : ResourceOrTag) : Prog grade Int32 := do
  emit <| Command.Declarations.locateBiome.call <| .cons (encode target) .nil

/-- Locate a point-of-interest ID or tag within the native 256-block search radius,
regardless of occupancy. Returns floored horizontal distance even when the POI differs in Y. -/
public def poi (target : ResourceOrTag) : Prog grade Int32 := do
  emit <| Command.Declarations.locatePoi.call <| .cons (encode target) .nil

end Oria.Std.Locate
