# Tags, titles, and sound

These modules support entity grouping and player feedback for Minecraft Java 26.3 / DP121.
They return `Prog g Int32`, use ordinary do notation, and retain native result and failure
behavior. The [checked examples](../Oria/Examples/StandardLibrary.lean) include a round
announcement and a dynamic action-bar counter.

## Entity tags

```lean
open Oria Oria.Std

example := Tag.add .self "game.playing"
example := Tag.remove (.selector .allPlayers) "game.playing"
example := Tag.list (.selector .allPlayers)
```

Tag names use `Command.Word`, a nonempty Brigadier unquoted word. String literals are checked
through the existing literal interface; computed host strings use `Command.Word.parse`.
The alphabet is shared with structured selector filters. Native selectors additionally
assign a meaning to empty tag filters, which do not name a tag for add/remove.

Add and remove return the number of entities changed and fail if none change. Duplicate adds,
missing-tag removals, and tag-capacity failures therefore compose through the existing failure
path. An empty entity selection fails. List returns the size of the union of tag names, rather
than a sum of per-entity counts. Existing entities without tags produce a successful zero.
Actual tag names can be read separately through entity NBT.

## Titles and action bars

```lean
example := Title.show .all (.literal "Round start")
example := Title.show .self (.literal "Choose a move") .subtitle
example (n : Val Int32) := Title.show .all (.number (.dynamic n)) .actionbar
example := Title.show .self (.ofNbt (nbt% {text: "Ready", color: "gold", bold: true}))
example := Title.clear .all
example := Title.clear .all (reset := true)
```

`TextComponent` is shared with Tellraw. Literal text and integer interpolation add no context
requirements, so they can run in server callbacks when their target selection permits it.
`ofNbt` accepts full host NBT text components and conservatively requires the full context.
The location is a host choice: title, subtitle, or actionbar.

Title operations return the number of packet recipients. Repeating a clear still succeeds
for an existing player selection. Clear removes title and subtitle text; reset also restores
native timings. Action-bar display has its own client lifetime. Packet delivery does not
prove that a client rendered the content.

```lean
example (stay : Val Int32) :=
  Title.times .all (.seconds (.decimal 0.25)) (.ticks (.dynamic stay)) (.days (.decimal 0.001))
```

`Time` represents the native time grammar: ticks (`t`), seconds (`s`), and days (`d`). Minecraft
parses a Float32 count, multiplies by 1, 20, or 24000, and rounds to an integer tick count.
Title timings require a nonnegative result. The example yields 5 ticks of fade-in, a dynamic
stay, and 24 ticks of fade-out. These are client animation settings, not a suspension of the
current Oria invocation. Effect's `Duration` type represents its separate integer/infinite grammar.

## Sound playback

```lean
example := Sound.play .self "minecraft:ui.button.click" .ui
example := Sound.play .all "game:round_start" .master
  {volume := .decimal 0.5, pitch := .decimal 1.25, minVolume := .decimal 0.25}
```

The category defaults to master. `SoundSettings` defaults to the execution position, volume 1,
pitch 1, and minVolume 0. It reuses Vec3 and Decimal, so coordinates and numeric parameters
can mix host fractions with dynamic I32 values. Native Float32 parsing requires volume ≥ 0,
pitch in 0..2, and minVolume in 0..1.

Minecraft sends packets only to selected players in the source dimension. Players outside
the native attenuation range are skipped unless minVolume is positive. For such a distant
player, the packet uses minVolume and an origin two blocks from that player toward the original
sound position. The result counts delivered packets; no qualifying recipient fails. Client
assets, volume settings, and playback determine whether the sound is audible. Custom sound IDs
can come from a resource pack.

`Execute.as` supplies an executor and preserves position. To originate a cue at every player,
use `Execute.forEach [.as .allPlayers, .at .self]` with `Sound.play .self` in its body. The compiler
checks the required context fields; selecting a player does not implicitly move the sound.

## Stop filters

```lean
example := Sound.stop .all
example := Sound.stop .all (some .music)
example := Sound.stop .all (sound := some "game:round_start")
example := Sound.stop .all (some .music) (some "game:round_start")
```

Category and sound ID filters are independent. The sound-only form emits the native wildcard
category. Stop requests are delivered across dimensions and return the target player count,
including when no matching sound is playing. Empty player selections fail.

## Compiler and verification

HUD and sound operations use distinct `Eff.hud` and `Eff.sound` labels. Their other effect bounds
cover world access, score reads, and randomness in argument evaluation. Playback additionally
requires its source dimension; coordinate and selector requirements are retained by their codecs.

All operations use existing command templates, command-component demand analysis, macros, and register/stack
allocation. Word validation, time units, text components, and numeric codecs are shared library
structures. Time and scalar bounds are validated by Minecraft when parsing commands. Invalid
static syntax can prevent a function from loading; invalid macro arguments fail on invocation.

`StdPresentation` checks lexical contracts, context requirements, and generated command text.
The [golden snapshot](../tests/golden/presentation.dp121) records a stack-backed compilation.
`scripts/rps-test` inspects actual native tag state and client packets through
`PresentationAcceptance.java`: partial tag updates, successful zero, title locations and styles,
time conversion, dynamic bounds failures, sound distance/dimension filtering, relocation,
independent stop filters, failure propagation, and explicit recovery.

The contracts follow TagCommand, TitleCommand, TimeArgument, PlaySoundCommand, StopSoundCommand,
and SoundSource in the server pinned by [minecraft-26.3.lock.json](../minecraft-26.3.lock.json).
