module

public import Oria.Std.Command.Arg.Server
import Oria.Std.Command.Declarations.Server
meta import Oria.Meta.Elab.ProgDo

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Profile and address bans

Bans and pardons require administrator permission (level 3). Profile lookup reuses Profiles;
ban-ip accepts a typed IPv4 address or an online player's name. Native reasons use Message.
An address ban may succeed with zero disconnected players.
-/

namespace Oria.Std.Admin.Ban
open Oria.Std.Command.Arg
open Oria.Command (encode emit)

/-- Context from profile or reason selection, with admission and disconnection effects. -/
@[expose] public def grade (req : ReqRow := Req.none) (reason : Option Message := none) : Grade :=
  ⟨req ||| (reason.map Message.requirements).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat ||| Eff.failure⟩

/-- Ban profiles and disconnect matching online players. Returns the newly banned profile count;
already banned profiles are skipped, and zero new bans fails. -/
public def players (profiles : Profiles) (reason : Option Message := none) :
    Prog (grade profiles.requirements reason) Int32 :=
  match reason with
  | none => do emit <| Command.Declarations.banPlayers.call <| .cons (encode profiles) <| .nil
  | some message => do emit <| Command.Declarations.banPlayersReason.call <| .cons (encode profiles) <| .cons (encode message) <| .nil

/-- Ban an address, returning the number of online players disconnected. Zero is a success.
An existing ban or unresolved online name fails. -/
public def ip (target : IpTarget) (reason : Option Message := none) :
    Prog (grade Req.none reason) Int32 :=
  match reason with
  | none => do emit <| Command.Declarations.banIp.call <| .cons (encode target) <| .nil
  | some message => do emit <| Command.Declarations.banIpReason.call <| .cons (encode target) <| .cons (encode message) <| .nil

/-- The native ban-list selection. -/
public inductive Filter where
  /-- Profile and address bans. -/
  | all
  /-- Profile bans. -/
  | players
  /-- Address bans. -/
  | ips

/-- Return the selected ban count. Empty lists succeed; names are source feedback. -/
public def list (filter : Filter := .all) : Prog grade Int32 :=
  match filter with
  | .all => do emit <| Command.Declarations.banList.call <| .nil
  | .players => do emit <| Command.Declarations.banListPlayers.call <| .nil
  | .ips => do emit <| Command.Declarations.banListIps.call <| .nil

/-- Remove profile bans and return their count. Fails when none of the profiles is banned. -/
public def pardon (profiles : Profiles) : Prog (grade profiles.requirements) Int32 := do
  emit <| Command.Declarations.pardonPlayers.call <| .cons (encode profiles) <| .nil

/-- Remove one IPv4 ban and return 1. Fails when the address is not banned. -/
public def pardonIp (address : _root_.Std.Net.IPv4Addr) : Prog grade Int32 := do
  emit <| Command.Declarations.pardonIp.call <| .cons (encode address) <| .nil

end Oria.Std.Admin.Ban
