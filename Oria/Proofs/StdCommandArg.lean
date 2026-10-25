module

import Oria.Std.Command.Arg.Position
meta import Oria.Meta.Elab.ProgDo

namespace Oria.Proofs.StdCommandArg

open Oria
open Oria.Std.Command.Arg

example (n : Nat) : (OfNat.ofNat n : Scalar) = .static (Int32.ofNat n) := rfl
example (n : Nat) : (OfNat.ofNat n : Decimal) = .static (Int32.ofNat n) := rfl
example (n : Int32) : (n : Scalar) = .static n := rfl
example (n : Int32) : (n : Decimal) = .static n := rfl
example (n : Float) : (n : Decimal) = .decimal n := rfl
example (n : Float32) : (n : Decimal) = .decimal n.toFloat := rfl
example {r : Region} (n : Val Int32 r) : (n : Scalar) = .dynamic n := rfl
example {r : Region} (n : Val Int32 r) : (n : Decimal) = .dynamic n := rfl
example (n : Int32) : (-(n : Scalar)) = .static (-n) := rfl
example (n : Float) : (-(n : Decimal)) = .decimal (-n) := rfl
example (n : Val Int32) : (-Scalar.dynamic n) = .dynamic (-n) := rfl
example (n : Val Int32) : (-Decimal.dynamic n) = .dynamic (-n) := rfl
example (m : Nat) (s : Bool) (e : Nat) :
    (OfScientific.ofScientific m s e : Decimal) =
      .decimal (OfScientific.ofScientific m s e : Float) := rfl
example (x y z : Decimal) : (Vec3.absolute x y z).requirements = Req.none := by
  simp [Vec3.requirements, Vec3.absolute, Command.encode, Command.ArgCodec.encode,
    Command.EncodedArg.requirements, Command.Fragment.spaced, Command.Fragment.append,
    Command.Fragment.space, Req.none]
example (x y z : Decimal) : (Vec3.relative x y z).requirements = Req.position := by
  simp [Vec3.requirements, Vec3.relative, Command.encode, Command.ArgCodec.encode,
    Command.EncodedArg.requirements, Command.Fragment.spaced, Command.Fragment.append,
    Command.Fragment.prepend, Command.Fragment.require, Command.Fragment.token,
    Command.Fragment.space, Req.none]
example (x y z : Scalar) :
    BlockPos.absolute x y z = .world (.absolute x) (.absolute y) (.absolute z) := rfl
example (x y z : Scalar) :
    BlockPos.relative x y z = .world (.relative x) (.relative y) (.relative z) := rfl

private def mixedPosition (x : Val Int32) : Vec3 :=
  .world (.relative x) (.absolute 80) (.relative 0)

private abbrev positionSig : Command.Signature :=
  { schema := [(Command.ArgCodec.key (A := Vec3))]
    req := Req.position ||| Req.rotation
    eff := Eff.world }

private def positionKeyword : Command.SyntaxToken :=
  .ofString "position"

private def positionTemplate : Command.Template [(Command.ArgCodec.key (A := Vec3))] :=
  { parts := [.token positionKeyword, .space, .slot ⟨0, by simp⟩] }

private def position : Command.Ref positionSig :=
  ⟨`proof.position, positionTemplate, none⟩

example (x : Val Int32) :
    Prog positionSig.grade Int32 := do
  Command.emit <| position.call (.cons (Command.encode (mixedPosition x)) .nil)

end Oria.Proofs.StdCommandArg
