module

public import Oria.Proofs.Fixtures.Batch.Common
public import Oria.Datapack
public meta import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Server
open Oria.Std Oria.Std.Command.Arg Oria.Datapack
open Oria.Proofs.Fixtures.Batch (capture input setup)


@[mcfunction]
public def packs := capture (PackControl.list)

@[mcfunction]
public def packsEnabled := capture (PackControl.list .enabled)

@[mcfunction]
public def packsAvailable := capture (PackControl.list .available)

@[mcfunction]
public def tickQuery := capture (Admin.Tick.run .query)

@[mcfunction]
public def tickRate := capture (Admin.Tick.run (.rate (.decimal 30.5)))

@[mcfunction]
public def tickFreeze := capture (Admin.Tick.run .freeze)

@[mcfunction]
public def tickUnfreeze := capture (Admin.Tick.run .unfreeze)

@[mcfunction]
public def tickStep := capture (Admin.Tick.run (.step (.ticks (.static 3))))

@[mcfunction]
public def tickStopStep := capture (Admin.Tick.run .stopStep)

@[mcfunction]
public def tickSprint := capture (Admin.Tick.run (.sprint (.seconds (.static 1))))

@[mcfunction]
public def tickStopSprint := capture (Admin.Tick.run .stopSprint)

@[mcfunction]
public def kick := capture (Admin.Kick.run .self)

@[mcfunction]
public def kickReason := capture (Admin.Kick.run .self (some (Message.join "Goodbye" [.selector .self])))

@[mcfunction]
public def transfer := capture (Admin.Transfer.to {host := "play.example.invalid"})

@[mcfunction]
public def transferAll := capture (Admin.Transfer.to {host := "play.example.invalid", port := .static 25566} .all)

@[mcfunction]
public def whitelistOn := capture (Admin.Whitelist.set true)

@[mcfunction]
public def whitelistOff := capture (Admin.Whitelist.set false)

@[mcfunction]
public def whitelistList := capture (Admin.Whitelist.list)

@[mcfunction]
public def whitelistReload := capture (Admin.Whitelist.reload)

@[mcfunction]
public def whitelistAdd := capture (Admin.Whitelist.add (.named "AdminGhost"))

@[mcfunction]
public def whitelistRemove := capture (Admin.Whitelist.remove (.named "AdminGhost"))

@[mcfunction]
public def whitelistAddPlayers := capture (Admin.Whitelist.add (.players .all))

@[mcfunction]
public def whitelistRemovePlayers := capture (Admin.Whitelist.remove (.players .all))

@[mcfunction]
public def ban := capture (Admin.Ban.players (.named "AdminGhost"))

@[mcfunction]
public def banReason := capture (Admin.Ban.players (.named "AdminGhost") (some "Testing policy"))

@[mcfunction]
public def pardon := capture (Admin.Ban.pardon (.named "AdminGhost"))

@[mcfunction]
public def banIp := capture (Admin.Ban.ip (.address (.ofParts 192 0 2 1)))

@[mcfunction]
public def banIpReason := capture (Admin.Ban.ip (.address (.ofParts 192 0 2 1)) (some "Testing policy"))

@[mcfunction]
public def pardonIp := capture (Admin.Ban.pardonIp (.ofParts 192 0 2 1))

@[mcfunction]
public def banList := capture (Admin.Ban.list)

@[mcfunction]
public def banListPlayers := capture (Admin.Ban.list .players)

@[mcfunction]
public def banListIps := capture (Admin.Ban.list .ips)

@[mcfunction]
public def op := capture (Admin.Operator.grant (.named "AdminGhost"))

@[mcfunction]
public def deop := capture (Admin.Operator.revoke (.named "AdminGhost"))

@[mcfunction]
public def idleTimeout := capture (Admin.IdleTimeout.set (.static 5))

@[mcfunction]
public def idleOff := capture (Admin.IdleTimeout.set (.static 0))

@[mcfunction]
public def objectives := capture (Scoreboard.Objectives.list)

@[mcfunction]
public def holders := capture (Scoreboard.list)

@[mcfunction]
public def scores := capture (Scoreboard.list (some (.named "#server")))

@[mcfunction]
public def groupSet := capture (Scoreboard.Group.set {holders := .entities (.selector .allPlayers), objective := "server.scores"} (.static 4))

@[mcfunction]
public def groupReset := capture (Scoreboard.Group.reset {holders := .entities (.selector .allPlayers), objective := "server.scores"})

@[mcfunction]
public def groupResetAll := capture (Scoreboard.Group.resetAll (.entities (.selector .allPlayers)))

@[mcfunction]
public def groupEnable := capture (Scoreboard.Group.enable {holders := .entities (.selector .allPlayers), objective := "server.trigger"})

@[mcfunction]
public def groupAdd := capture (Scoreboard.Group.operation {holders := .entities (.selector .allPlayers), objective := "server.scores"} .add {holders := .one (.named "#server"), objective := "server.scores"})

@[mcfunction]
public def groupSwap := capture (Scoreboard.Group.operation {holders := .one (.named "#left"), objective := "server.scores"} .swap {holders := .one (.named "#right"), objective := "server.scores"})

@[mcfunction]
public def groupDivideZero := capture (Scoreboard.Group.operation {holders := .one (.named "#left"), objective := "server.scores"} .divide {holders := .one (.named "#zero"), objective := "server.scores"})

@[mcfunction]
public def groupAbsent := capture (Scoreboard.Group.set {holders := .entities (.selector (.allPlayers {tags := [.include "server.absent"]})), objective := "server.scores"} (.static 4))

@[mcfunction]
public def tickDynamic := input (g := Admin.Tick.grade) fun n => do
  Admin.Tick.run (.rate (.dynamic n))

@[mcfunction]
public def transferDynamic := input (g := Admin.Transfer.grade .all) fun n => do
  Admin.Transfer.to {host := "play.example.invalid", port := .dynamic n} .all

@[mcfunction]
public def idleDynamic := input (g := Admin.IdleTimeout.grade) fun n => do
  Admin.IdleTimeout.set (.dynamic n)

@[mcfunction]
public def groupDynamic := input (g := Scoreboard.Group.grade Req.none) fun n => do
  Scoreboard.Group.set {holders := .entities (.selector .allPlayers), objective := "server.scores"} (.dynamic n)

@[datapack]
public def specimen : Spec := build {ns := "servercmd", registerBudget := 6} do
  onLoad setup.ref
  entry "packs" packs.ref
  entry "packsenabled" packsEnabled.ref
  entry "packsavailable" packsAvailable.ref
  entry "tickquery" tickQuery.ref
  entry "tickrate" tickRate.ref
  entry "tickfreeze" tickFreeze.ref
  entry "tickunfreeze" tickUnfreeze.ref
  entry "tickstep" tickStep.ref
  entry "tickstopstep" tickStopStep.ref
  entry "ticksprint" tickSprint.ref
  entry "tickstopsprint" tickStopSprint.ref
  entry "kick" kick.ref
  entry "kickreason" kickReason.ref
  entry "transfer" transfer.ref
  entry "transferall" transferAll.ref
  entry "whiteliston" whitelistOn.ref
  entry "whitelistoff" whitelistOff.ref
  entry "whitelistlist" whitelistList.ref
  entry "whitelistreload" whitelistReload.ref
  entry "whitelistadd" whitelistAdd.ref
  entry "whitelistremove" whitelistRemove.ref
  entry "whitelistaddplayers" whitelistAddPlayers.ref
  entry "whitelistremoveplayers" whitelistRemovePlayers.ref
  entry "ban" ban.ref
  entry "banreason" banReason.ref
  entry "pardon" pardon.ref
  entry "banip" banIp.ref
  entry "banipreason" banIpReason.ref
  entry "pardonip" pardonIp.ref
  entry "banlist" banList.ref
  entry "banlistplayers" banListPlayers.ref
  entry "banlistips" banListIps.ref
  entry "op" op.ref
  entry "deop" deop.ref
  entry "idletimeout" idleTimeout.ref
  entry "idleoff" idleOff.ref
  entry "objectives" objectives.ref
  entry "holders" holders.ref
  entry "scores" scores.ref
  entry "groupset" groupSet.ref
  entry "groupreset" groupReset.ref
  entry "groupresetall" groupResetAll.ref
  entry "groupenable" groupEnable.ref
  entry "groupadd" groupAdd.ref
  entry "groupswap" groupSwap.ref
  entry "groupdividezero" groupDivideZero.ref
  entry "groupabsent" groupAbsent.ref
  entry "tickdynamic" tickDynamic.ref
  entry "transferdynamic" transferDynamic.ref
  entry "idledynamic" idleDynamic.ref
  entry "groupdynamic" groupDynamic.ref

end Oria.Proofs.Fixtures.Server
