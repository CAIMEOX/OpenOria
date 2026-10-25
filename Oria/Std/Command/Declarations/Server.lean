module

public import Oria.Std.Command.Arg.Server

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations
open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Count enabled and compatible available packs. -/
@[expose] public def packList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.packList
    template := .positional ["datapack", "list"] }

/-- Count compatible, currently disabled packs. -/
@[expose] public def packListAvailable : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.packListAvailable
    template := .positional ["datapack", "list", "available"] }

/-- Count enabled packs. -/
@[expose] public def packListEnabled : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.packListEnabled
    template := .positional ["datapack", "list", "enabled"] }

/-- Operate on the server tick manager. -/
@[expose] public def tick : Oria.Command.Ref {
    schema := [ArgCodec.key (A := TickAction)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.tick
    template := .positional ["tick"] }

/-- Disconnect selected players with the native default reason. -/
@[expose] public def kick : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.kick
    template := .positional ["kick"] }

/-- Disconnect selected players with a native message reason. -/
@[expose] public def kickReason : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := Message)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.kickReason
    template := .positional ["kick"] }

/-- Send transfer packets to selected players. -/
@[expose] public def transfer : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Destination), ArgCodec.key (A := Players)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.transfer
    template := .positional ["transfer"] }

/-- Enable the whitelist and enforce admission. -/
@[expose] public def whitelistOn : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.whitelistOn
    template := .positional ["whitelist", "on"] }

/-- Disable the whitelist. -/
@[expose] public def whitelistOff : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.whitelistOff
    template := .positional ["whitelist", "off"] }

/-- Count whitelisted profiles. -/
@[expose] public def whitelistList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.whitelistList
    template := .positional ["whitelist", "list"] }

/-- Reload whitelist data and enforce admission. -/
@[expose] public def whitelistReload : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.whitelistReload
    template := .positional ["whitelist", "reload"] }

/-- Add selected profiles to the whitelist. -/
@[expose] public def whitelistAdd : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.whitelistAdd
    template := .positional ["whitelist", "add"] }

/-- Remove selected profiles from the whitelist. -/
@[expose] public def whitelistRemove : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.whitelistRemove
    template := .positional ["whitelist", "remove"] }

/-- Ban selected profiles with the native default reason. -/
@[expose] public def banPlayers : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banPlayers
    template := .positional ["ban"] }

/-- Ban selected profiles with a native message reason. -/
@[expose] public def banPlayersReason : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles), ArgCodec.key (A := Message)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banPlayersReason
    template := .positional ["ban"] }

/-- Ban an address and disconnect players using it. -/
@[expose] public def banIp : Oria.Command.Ref {
    schema := [ArgCodec.key (A := IpTarget)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banIp
    template := .positional ["ban-ip"] }

/-- Ban an address with a native message reason. -/
@[expose] public def banIpReason : Oria.Command.Ref {
    schema := [ArgCodec.key (A := IpTarget), ArgCodec.key (A := Message)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banIpReason
    template := .positional ["ban-ip"] }

/-- Count profile and IP bans. -/
@[expose] public def banList : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banList
    template := .positional ["banlist"] }

/-- Count profile bans. -/
@[expose] public def banListPlayers : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banListPlayers
    template := .positional ["banlist", "players"] }

/-- Count address bans. -/
@[expose] public def banListIps : Oria.Command.Ref {
    schema := []
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.banListIps
    template := .positional ["banlist", "ips"] }

/-- Remove selected profile bans. -/
@[expose] public def pardonPlayers : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.pardonPlayers
    template := .positional ["pardon"] }

/-- Remove one IPv4 ban. -/
@[expose] public def pardonIp : Oria.Command.Ref {
    schema := [ArgCodec.key (A := _root_.Std.Net.IPv4Addr)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.chat
  } := {
    key := `minecraft.std.pardonIp
    template := .positional ["pardon-ip"] }

/-- Grant operator status to selected profiles. -/
@[expose] public def op : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.op
    template := .positional ["op"] }

/-- Revoke operator status and enforce admission. -/
@[expose] public def deop : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Profiles)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.random
  } := {
    key := `minecraft.std.deop
    template := .positional ["deop"] }

/-- Set the idle timeout in minutes. -/
@[expose] public def idleTimeout : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world
  } := {
    key := `minecraft.std.idleTimeout
    template := .positional ["setidletimeout"] }

/-- Server interaction and administration declarations. -/
@[expose] public def server : List Oria.Command.Decl :=
  [packList.declaration,
    packListAvailable.declaration,
    packListEnabled.declaration,
    tick.declaration,
    kick.declaration,
    kickReason.declaration,
    transfer.declaration,
    whitelistOn.declaration,
    whitelistOff.declaration,
    whitelistList.declaration,
    whitelistReload.declaration,
    whitelistAdd.declaration,
    whitelistRemove.declaration,
    banPlayers.declaration,
    banPlayersReason.declaration,
    banIp.declaration,
    banIpReason.declaration,
    banList.declaration,
    banListPlayers.declaration,
    banListIps.declaration,
    pardonPlayers.declaration,
    pardonIp.declaration,
    op.declaration,
    deop.declaration,
    idleTimeout.declaration]

end Oria.Std.Command.Declarations
