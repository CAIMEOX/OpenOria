module

import Oria
import Oria.Std.Manifest
meta import Oria.Std.Manifest

namespace Oria.Proofs.StdBatch

open Oria.Std Oria.Std.Command.Arg

example : (Weather.grade none).req = Req.dimension := rfl
example : (Weather.grade (some (.ticks (.static 20)))).req = Req.none := rfl
example : (Weather.grade (some (.ticks (.static 20)))).eff = Eff.world ||| Eff.failure := rfl
example : (Time.grade (some (ResourceId.ofString "minecraft:overworld"))).req = Req.none := rfl
example : (Time.grade none).req = Req.dimension := rfl
example : Difficulty.writeGrade.req = Req.none := rfl
example : (Experience.grade .self).req = Req.executor := rfl
example : (GameMode.grade .all).req = Req.none := rfl
example : (Bossbar.grade Req.none).req = Req.none := rfl
example : (Holders.one (.named (ScoreHolderName.ofString "#bot"))).requirements = Req.none := rfl
example : (Holders.entities (.selector .allPlayers)).requirements = Req.none := rfl
example : (BarProperty.players none).requirements = Req.none := rfl
example : (BarProperty.name (.literal "Round")).requirements = Req.none := rfl
example : (TeamProperty.prefix (.literal "[R]")).requirements = Req.none := rfl
example (scope : AdvancementScope) : (Command.encode scope).requirements = Req.none := rfl

#guard Std.Manifest.commandDeclarations.length == 176
#guard Std.Manifest.commandCatalog.isOk

end Oria.Proofs.StdBatch
