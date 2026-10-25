module

public import Oria.Std.Command.Arg.Block

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# World-generation arguments

Template settings preserve native argument order. Every setting has its native default,
so a caller can choose strict placement or a seed without supplying intermediate arguments.
Block coordinates, feature descriptions, and runtime integer holes use shared codecs.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode)

/-- Quarter-turn rotation of blocks and structures around the placement origin. -/
public inductive QuarterTurn where
  /-- Preserve orientation. -/
  | none
  /-- Rotate 90 degrees clockwise. -/
  | clockwise90
  /-- Rotate 180 degrees. -/
  | clockwise180
  /-- Rotate 90 degrees counterclockwise. -/
  | counterclockwise90

public instance : Oria.Command.ArgCodec QuarterTurn where
  key := ⟨`minecraft.argument.template_rotation⟩
  encode r := .token (match r with
    | .none => "none" | .clockwise90 => "clockwise_90"
    | .clockwise180 => "180" | .counterclockwise90 => "counterclockwise_90")

/-- Native template reflection, applied before rotation. -/
public inductive Mirror where
  /-- Preserve the template. -/
  | none
  /-- Reflect the Z coordinate. -/
  | leftRight
  /-- Reflect the X coordinate. -/
  | frontBack

public instance : Oria.Command.ArgCodec Mirror where
  key := ⟨`minecraft.argument.mirror⟩
  encode m := .token (match m with
    | .none => "none" | .leftRight => "left_right" | .frontBack => "front_back")

/-- Structure-template placement settings. The game checks integrity and seed bounds. -/
public structure TemplateSettings where
  /-- Rotation around the placement origin. -/
  rotation : QuarterTurn := .none
  /-- Reflection before rotation. -/
  mirror : Mirror := .none
  /-- Block retention probability, parsed as Float32 in the inclusive interval 0..1. -/
  integrity : Decimal := .static 1
  /-- Native signed I32 seed. Zero selects the native time-derived random source. -/
  seed : Scalar := .static 0
  /-- Suppress native neighbor and shape updates during placement. -/
  strict : Bool := false

public instance : Oria.Command.ArgCodec TemplateSettings where
  key := ⟨`minecraft.argument.template_settings⟩
  encode s :=
    let f := Oria.Command.Fragment.spaced ([
      (encode s.rotation).fragment, (encode s.mirror).fragment,
      (encode s.integrity).fragment, (encode s.seed).fragment] ++
      if s.strict then [.token "strict"] else [])
    ⟨f.segments, Req.none⟩

@[simp] public theorem TemplateSettings.encode_requirements (s : TemplateSettings) :
    (encode s).requirements = Req.none := rfl

@[simp] public theorem TemplateSettings.encode_fragment_requirements (s : TemplateSettings) :
    (encode s).fragment.requirements = Req.none := rfl

end Oria.Std.Command.Arg
