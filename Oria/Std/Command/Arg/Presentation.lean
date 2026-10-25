module

public import Oria.Std.Command.Arg.Text

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Presentation arguments

Title locations and sound channels are host choices. Playback parameters combine existing
coordinate and Decimal codecs, so dynamic integer components introduce ordinary macro holes.
Time arguments use the shared ticks/seconds/days codec in Command.Arg.Numeric.
-/

namespace Oria.Std.Command.Arg

/-- Destination of a title text component. -/
public inductive TitlePart where
  /-- Main centered title. -/
  | title
  /-- Subtitle displayed with the main title. -/
  | subtitle
  /-- Text above the hotbar, independent of title timings. -/
  | actionbar

public instance : Oria.Command.ArgCodec TitlePart where
  key := ⟨`minecraft.argument.title_part⟩
  encode part := .token (match part with
    | .title => "title" | .subtitle => "subtitle" | .actionbar => "actionbar")

@[simp] public theorem TitlePart.encode_requirements (part : TitlePart) :
    (Oria.Command.encode part).requirements = Req.none := rfl

@[simp] public theorem TitlePart.encode_fragment_requirements (part : TitlePart) :
    (Oria.Command.encode part).fragment.requirements = Req.none := rfl

/-- Native sound categories, including the DP121 UI category. -/
public inductive SoundChannel where
  /-- Master volume. -/
  | master
  /-- Music. -/
  | music
  /-- Music discs. -/
  | record
  /-- Weather. -/
  | weather
  /-- Blocks. -/
  | block
  /-- Hostile creatures. -/
  | hostile
  /-- Neutral creatures. -/
  | neutral
  /-- Players. -/
  | player
  /-- Ambient sounds. -/
  | ambient
  /-- Voice. -/
  | voice
  /-- User interface sounds. -/
  | ui

public instance : Oria.Command.ArgCodec SoundChannel where
  key := ⟨`minecraft.argument.sound_source⟩
  encode channel := .token (match channel with
    | .master => "master" | .music => "music" | .record => "record"
    | .weather => "weather" | .block => "block" | .hostile => "hostile"
    | .neutral => "neutral" | .player => "player" | .ambient => "ambient"
    | .voice => "voice" | .ui => "ui")

@[simp] public theorem SoundChannel.encode_requirements (channel : SoundChannel) :
    (Oria.Command.encode channel).requirements = Req.none := rfl

@[simp] public theorem SoundChannel.encode_fragment_requirements (channel : SoundChannel) :
    (Oria.Command.encode channel).fragment.requirements = Req.none := rfl

/-- Playback parameters. Native parsing checks volume ≥ 0, pitch in 0..2, and minVolume
in 0..1. Numeric parameters use Float32 parsing in Minecraft. -/
public structure SoundSettings where
  /-- Origin of the sound, defaulting to the execution position. -/
  position : Vec3 := .world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0))
  /-- Volume and native attenuation range multiplier. -/
  volume : Decimal := .static 1
  /-- Pitch multiplier. -/
  pitch : Decimal := .static 1
  /-- Positive values permit delivery beyond the normal range at a relocated sound position. -/
  minVolume : Decimal := .static 0

public instance : Oria.Command.ArgCodec SoundSettings where
  key := ⟨`minecraft.argument.sound_settings⟩
  encode settings := .spaced [
    (Oria.Command.encode settings.position).fragment,
    (Oria.Command.encode settings.volume).fragment,
    (Oria.Command.encode settings.pitch).fragment,
    (Oria.Command.encode settings.minVolume).fragment]

/-- Execution context needed by the sound's coordinates. Numeric parameters add no requirements. -/
@[expose] public def SoundSettings.requirements (settings : SoundSettings) : ReqRow :=
  (Oria.Command.encode settings).requirements

end Oria.Std.Command.Arg
