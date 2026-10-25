module

public import Oria.Std.Command.Arg.Text

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

namespace Oria.Std.Command.Arg

/-- Native weather mode. -/
public inductive WeatherKind where
  /-- clear. -/
  | clear
  /-- rain. -/
  | rain
  /-- thunder. -/
  | thunder
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec WeatherKind where
  key := ⟨`minecraft.argument.weatherkind⟩
  encode value := .token (match value with
    | .clear => "clear"
    | .rain => "rain"
    | .thunder => "thunder")

@[simp] public theorem WeatherKind.encode_requirements (value : WeatherKind) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem WeatherKind.encode_fragment_requirements (value : WeatherKind) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

/-- Server difficulty. -/
public inductive DifficultyLevel where
  /-- peaceful. -/
  | peaceful
  /-- easy. -/
  | easy
  /-- normal. -/
  | normal
  /-- hard. -/
  | hard
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec DifficultyLevel where
  key := ⟨`minecraft.argument.difficultylevel⟩
  encode value := .token (match value with
    | .peaceful => "peaceful"
    | .easy => "easy"
    | .normal => "normal"
    | .hard => "hard")

@[simp] public theorem DifficultyLevel.encode_requirements (value : DifficultyLevel) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem DifficultyLevel.encode_fragment_requirements (value : DifficultyLevel) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl


/-- A clock operation. Time values are parsed by the native time parser. -/
public inductive ClockAction where
  /-- Set total ticks. -/
  | set : Time → ClockAction
  /-- Advance or rewind by a signed duration. -/
  | add : Time → ClockAction
  /-- Set time using a marker such as minecraft:day. -/
  | marker : ResourceId → ClockAction
  /-- Pause the selected world clock. -/
  | pause
  /-- Resume the selected world clock. -/
  | resume
  /-- Set a Float32 rate from 0.00001 to 1000. -/
  | rate : Decimal → ClockAction
  /-- Query total ticks, modulo 2147483647. -/
  | query
  /-- Query ticks within a timeline, or its repetition count when true. -/
  | timeline : ResourceId → Bool → ClockAction

public instance : Oria.Command.ArgCodec ClockAction where
  key := ⟨`minecraft.argument.clock_action⟩
  encode action :=
    let fragment : Oria.Command.Fragment EncodedVal := match action with
      | .set t => .spaced [.token "set", (Oria.Command.encode t).fragment]
      | .add t => .spaced [.token "add", (Oria.Command.encode t).fragment]
      | .marker id => .spaced [.token "set", (Oria.Command.encode id).fragment]
      | .pause => .token "pause"
      | .resume => .token "resume"
      | .rate n => .spaced [.token "rate", (Oria.Command.encode n).fragment]
      | .query => .spaced [.token "query", .token "time"]
      | .timeline id repetition => .spaced
          ([.token "query", (Oria.Command.encode id).fragment] ++
            if repetition then [.token "repetition"] else [])
    ⟨fragment.segments, Req.none⟩

@[simp] public theorem ClockAction.encode_requirements (action : ClockAction) :
    (Oria.Command.encode action).requirements = Req.none := rfl

@[simp] public theorem ClockAction.encode_fragment_requirements (action : ClockAction) :
    (Oria.Command.encode action).fragment.requirements = Req.none := rfl

/-- Two world coordinates, ordered X then Z. -/
public structure Vec2 where
  /-- X component. -/
  x : WorldCoord
  /-- Z component. -/
  z : WorldCoord

public instance : Oria.Command.ArgCodec Vec2 where
  key := ⟨`minecraft.argument.vec2⟩
  encode p := .spaced [(Oria.Command.encode p.x).fragment, (Oria.Command.encode p.z).fragment]

/-- World-border operation in the source dimension. Native bounds and unchanged-state failures apply. -/
public inductive BorderAction where
  /-- Query rounded diameter. -/
  | get
  /-- Change the center. -/
  | center : Vec2 → BorderAction
  /-- Set diameter, with optional transition duration. -/
  | set : Decimal → Option Time → BorderAction
  /-- Change diameter by a signed amount, with optional transition duration. -/
  | add : Decimal → Option Time → BorderAction
  /-- Damage per block outside the buffer. -/
  | damage : Decimal → BorderAction
  /-- Safe buffer outside the border. -/
  | buffer : Decimal → BorderAction
  /-- Warning distance in blocks. -/
  | warningDistance : Scalar → BorderAction
  /-- Warning lead time. -/
  | warningTime : Time → BorderAction

public instance : Oria.Command.ArgCodec BorderAction where
  key := ⟨`minecraft.argument.border_action⟩
  encode
    | .get => .token "get"
    | .center p => .spaced [.token "center", (Oria.Command.encode p).fragment]
    | .set n t => .spaced ([.token "set", (Oria.Command.encode n).fragment] ++
        t.toList.map (fun v => (Oria.Command.encode v).fragment))
    | .add n t => .spaced ([.token "add", (Oria.Command.encode n).fragment] ++
        t.toList.map (fun v => (Oria.Command.encode v).fragment))
    | .damage n => .spaced [.token "damage", .token "amount", (Oria.Command.encode n).fragment]
    | .buffer n => .spaced [.token "damage", .token "buffer", (Oria.Command.encode n).fragment]
    | .warningDistance n => .spaced [.token "warning", .token "distance", (Oria.Command.encode n).fragment]
    | .warningTime t => .spaced [.token "warning", .token "time", (Oria.Command.encode t).fragment]

/-- Coordinate requirements carried by the selected operation. -/
@[expose] public def BorderAction.requirements (action : BorderAction) : ReqRow :=
  (Oria.Command.encode action).requirements

end Oria.Std.Command.Arg
