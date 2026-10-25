module
public import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Proofs.Fixtures.Batch.Common

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def weatherClear := capture (Weather.set .clear (some (.ticks (.static 200))))

@[mcfunction]
public def weatherRain := capture (Weather.set .rain (some (.seconds (.static 5))))

@[mcfunction]
public def weatherThunder := capture (Weather.set .thunder (some (.ticks (.static 300))))

@[mcfunction]
public def weatherSample := capture (Weather.set .clear)

@[mcfunction]
public def clockPause := capture (Time.run .pause (some "minecraft:overworld"))

@[mcfunction]
public def clockResume := capture (Time.run .resume (some "minecraft:overworld"))

@[mcfunction]
public def clockSet := capture (Time.run (.set (.ticks (.static 6000))) (some "minecraft:overworld"))

@[mcfunction]
public def clockAdd := capture (Time.run (.add (.ticks (.static (-100)))) (some "minecraft:overworld"))

@[mcfunction]
public def clockQuery := capture (Time.run .query (some "minecraft:overworld"))

@[mcfunction]
public def clockDefault := capture (Time.run .query)

@[mcfunction]
public def clockMarker := capture (Time.run (.marker "minecraft:day") (some "minecraft:overworld"))

@[mcfunction]
public def clockRate := capture (Time.run (.rate (.decimal 0.5)) (some "minecraft:overworld"))

@[mcfunction]
public def clockResetRate := capture (Time.run (.rate (.static 1)) (some "minecraft:overworld"))

@[mcfunction]
public def timelineTicks := capture (Time.run (.timeline "minecraft:day" false) (some "minecraft:overworld"))

@[mcfunction]
public def timelineRepetition := capture (Time.run (.timeline "minecraft:day" true) (some "minecraft:overworld"))

@[mcfunction]
public def gameTime := capture (Time.gameTime)

@[mcfunction]
public def difficultyGet := capture (Difficulty.get)

@[mcfunction]
public def difficultySet := capture (Difficulty.set .hard)

@[mcfunction]
public def defaultMode := capture (GameMode.setDefault .adventure)

@[mcfunction]
public def borderGet := capture (WorldBorder.run .get)

@[mcfunction]
public def borderSet := capture (WorldBorder.run (.set (.static 1000) none))

@[mcfunction]
public def borderAdd := capture (WorldBorder.run (.add (.static 100) none))

@[mcfunction]
public def borderCenter := capture (WorldBorder.run (.center ⟨.absolute (.decimal 10.5), .absolute (.decimal 20.5)⟩))

@[mcfunction]
public def borderBuffer := capture (WorldBorder.run (.buffer (.decimal 7.5)))

@[mcfunction]
public def borderDamage := capture (WorldBorder.run (.damage (.decimal 0.25)))

@[mcfunction]
public def borderWarningDistance := capture (WorldBorder.run (.warningDistance (.static 9)))

@[mcfunction]
public def borderWarningTime := capture (WorldBorder.run (.warningTime (.seconds (.static 2))))

@[mcfunction]
public def borderTransition := capture (WorldBorder.run (.set (.static 1200) (some (.seconds (.static 10)))))

@[mcfunction]
public def weatherDynamic := input (g := Weather.grade (some (.ticks (.static 1)))) (fun n => do Weather.set .rain (some (.ticks (.dynamic n))))

@[mcfunction]
public def clockDynamic := input (g := Time.grade (some "minecraft:overworld")) (fun n => do Time.run (.set (.ticks (.dynamic n))) (some "minecraft:overworld"))

@[mcfunction]
public def borderDynamic := input (g := WorldBorder.grade .get) (fun n => do WorldBorder.run (.set (.dynamic n) none))

@[mcfunction]
public def xpDynamic := input (g := Experience.grade .self) (fun n => do Experience.add .self (.dynamic n) .levels)

@[mcfunction]
public def enchantDynamic := input (g := Enchant.grade .self) (fun n => do Enchant.apply .self "minecraft:sharpness" (.dynamic n))

@[mcfunction]
public def damageDynamic := input (g := Damage.grade victim) (fun n => do Damage.apply victim (.dynamic n))

@[mcfunction]
public def barDynamic := input (g := Bossbar.grade) (fun n => do Bossbar.set "batch:bar" (.value (.dynamic n)))

end Oria.Proofs.Fixtures.Batch
