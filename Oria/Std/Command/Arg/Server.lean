module

public import Oria.Std.Command.Arg.Message
public import Std.Net.Addr

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Server command arguments

Profiles distinguish account lookup from online player selection. Network addresses reuse
Lean's Std.Net model. Quoting, numeric holes, and native messages reuse the command-fragment
serializers.
-/

namespace Oria.Std.Command.Arg

/-- Native account lookup or selection of online player profiles. -/
public inductive Profiles where
  /-- Account name; Minecraft resolves cached or offline profiles as configured. -/
  | named : Oria.Command.Word → Profiles
  /-- Online profiles selected through the shared player argument. -/
  | players : Players → Profiles

public instance : Oria.Command.ArgCodec Profiles where
  key := ⟨`minecraft.argument.game_profiles⟩
  encode
    | .named name => (Oria.Command.encode name).fragment
    | .players players => (Oria.Command.encode players).fragment

/-- Account names are context-independent; online selections retain their requirements. -/
@[expose] public def Profiles.requirements : Profiles → ReqRow
  | .named _ => Req.none
  | .players p => p.requirements

@[simp] public theorem Profiles.encode_requirements (p : Profiles) :
    (Oria.Command.encode p).requirements = p.requirements := by
  cases p <;> rfl

/-- An address accepted by the native unquoted IP command argument, or an online name.
The native word grammar admits IPv4 spelling; a player's current address is resolved by Minecraft. -/
public inductive IpTarget where
  /-- IPv4 address represented by the Lean standard library. -/
  | address : _root_.Std.Net.IPv4Addr → IpTarget
  /-- Online player's name, resolved to its current address by ban-ip. -/
  | player : Oria.Command.Word → IpTarget

public instance : Oria.Command.ArgCodec _root_.Std.Net.IPv4Addr where
  key := ⟨`minecraft.argument.ipv4⟩
  encode ip := ⟨[.literal (.unquoted (toString ip))], Req.none⟩

public instance : Oria.Command.ArgCodec IpTarget where
  key := ⟨`minecraft.argument.ip_target⟩
  encode target :=
    let f := match target with
      | .address ip => (Oria.Command.encode ip).fragment
      | .player name => (Oria.Command.encode name).fragment
    { f with requirements := Req.none }

@[simp] public theorem IpTarget.encode_requirements (target : IpTarget) :
    (Oria.Command.encode target).requirements = Req.none := rfl

/-- A transfer destination. Minecraft validates ports in 1 through 65535. -/
public structure Destination where
  /-- Hostname or address, using the native quoted-string parser. -/
  host : String
  /-- Static or runtime port. -/
  port : Scalar := .static 25565

public instance : Oria.Command.ArgCodec Destination where
  key := ⟨`minecraft.argument.transfer_destination⟩
  encode d :=
    let f := Oria.Command.Fragment.spaced
      [⟨[.literal (.quoted d.host)], Req.none⟩, (Oria.Command.encode d.port).fragment]
    { f with requirements := Req.none }

@[simp] public theorem Destination.encode_requirements (d : Destination) :
    (Oria.Command.encode d).requirements = Req.none := rfl

/-- Server tick operations. Counts use native time units and rounding. -/
public inductive TickAction where
  /-- Return the target rate truncated to I32; timing statistics are source feedback. -/
  | query
  /-- Set the target ticks per second, from 1 to 10000. -/
  | rate : Decimal → TickAction
  /-- Freeze simulation, stopping current stepping or sprinting. -/
  | freeze
  /-- Resume normal simulation. -/
  | unfreeze
  /-- Advance at least one tick while frozen. -/
  | step : Time → TickAction
  /-- Stop an active step request. -/
  | stopStep
  /-- Run a positive number of ticks as fast as possible. -/
  | sprint : Time → TickAction
  /-- Stop an active sprint. -/
  | stopSprint

public instance : Oria.Command.ArgCodec TickAction where
  key := ⟨`minecraft.argument.tick_action⟩
  encode a :=
    let f : Oria.Command.Fragment EncodedVal := match a with
      | .query => .token "query"
      | .rate n => .spaced [.token "rate", (Oria.Command.encode n).fragment]
      | .freeze => .token "freeze"
      | .unfreeze => .token "unfreeze"
      | .step t => .spaced [.token "step", (Oria.Command.encode t).fragment]
      | .stopStep => .spaced [.token "step", .token "stop"]
      | .sprint t => .spaced [.token "sprint", (Oria.Command.encode t).fragment]
      | .stopSprint => .spaced [.token "sprint", .token "stop"]
    { f with requirements := Req.none }

@[simp] public theorem TickAction.encode_requirements (a : TickAction) :
    (Oria.Command.encode a).requirements = Req.none := rfl

end Oria.Std.Command.Arg
