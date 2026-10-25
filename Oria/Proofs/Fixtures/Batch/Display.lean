module

public import Oria.Proofs.Fixtures.Batch.ControlCommon
public meta import Oria.Proofs.Fixtures.Batch.ControlCommon

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def particles := capture (Particle.send {id := "minecraft:flame"})

@[mcfunction]
public def particleDust := capture (Particle.send {id := "minecraft:dust", options := .value (nbt% {color: [1.0, 0.0, 0.0], scale: 1.0})})

@[mcfunction]
public def particleForce := capture (Particle.send {id := "minecraft:flame"} {force := true, count := .static 0})

@[mcfunction]
public def swingHand := capture (Swing.run)

@[mcfunction]
public def swingStab := capture (Swing.run .self {hand := .offhand, animation := .stab, duration := .seconds (.decimal 0.5)})

@[mcfunction]
public def swingNone := capture (Swing.run .self {animation := .none})

@[mcfunction]
public def swingMarker := capture (Swing.run
  (.selector (.allEntities {tags := [.include "control.marker"], limit := some 1})))

@[mcfunction]
public def postAdd := capture (PostEffect.add .all "batch:gray")

@[mcfunction]
public def postRemove := capture (PostEffect.remove .all "batch:gray")

@[mcfunction]
public def postClear := capture (PostEffect.clear .all)

@[mcfunction]
public def postList := capture (PostEffect.list)

@[mcfunction]
public def sidebar := capture (Scoreboard.Objectives.setDisplay .sidebar (some points))

@[mcfunction]
public def belowName := capture (Scoreboard.Objectives.setDisplay .belowName (some points))

@[mcfunction]
public def listDisplay := capture (Scoreboard.Objectives.setDisplay .list (some points))

@[mcfunction]
public def teamSidebar := capture (Scoreboard.Objectives.setDisplay (.sidebarTeam .red) (some points))

@[mcfunction]
public def clearSidebar := capture (Scoreboard.Objectives.setDisplay .sidebar)

@[mcfunction]
public def objectiveName := capture (Scoreboard.Objectives.modify points (.displayName (.literal "Control")))

@[mcfunction]
public def objectiveHearts := capture (Scoreboard.Objectives.modify points (.renderType .hearts))

@[mcfunction]
public def objectiveInteger := capture (Scoreboard.Objectives.modify points (.renderType .integer))

@[mcfunction]
public def objectiveAuto := capture (Scoreboard.Objectives.modify points (.autoUpdate false))

@[mcfunction]
public def objectiveBlank := capture (Scoreboard.Objectives.modify points (.numberFormat .blank))

@[mcfunction]
public def objectiveFixed := capture (Scoreboard.Objectives.modify points (.numberFormat (.fixed (.literal "Round"))))

@[mcfunction]
public def objectiveStyle := capture (Scoreboard.Objectives.modify points (.numberFormat (.styled (.value (nbt% {color: "gold", bold: true})))))

@[mcfunction]
public def objectiveFormatReset := capture (Scoreboard.Objectives.modify points (.numberFormat .reset))

@[mcfunction]
public def scoreName := capture (Scoreboard.setName (.entities (.selector .allPlayers)) points (some (.literal "Player")))

@[mcfunction]
public def scoreNameReset := capture (Scoreboard.setName (.entities (.selector .allPlayers)) points)

@[mcfunction]
public def scoreBlank := capture (Scoreboard.numberFormat (.entities (.selector .allPlayers)) points .blank)

@[mcfunction]
public def scoreFixed := capture (Scoreboard.numberFormat (.one (.named "#bot")) points (.fixed (.literal "Bot")))

@[mcfunction]
public def scoreStyle := capture (Scoreboard.numberFormat (.entities (.selector .allPlayers)) points (.styled (.value (nbt% {italic: true}))))

@[mcfunction]
public def scoreFormatReset := capture (Scoreboard.numberFormat (.entities (.selector .allPlayers)) points .reset)

@[mcfunction]
public def teamFilter := capture (Tellraw.text (.selector (.allPlayers {team := some (.include "batch.control")})) "Team")

@[mcfunction]
public def teamExclude := capture (Tellraw.text (.selector (.allPlayers {team := some (.exclude "batch.control")})) "Other")

@[mcfunction]
public def teamEmptyFilter := capture (Tellraw.text (.selector (.allPlayers {team := some (.include "")})) "Unassigned")

@[mcfunction]
public def teamAnyFilter := capture (Tellraw.text (.selector (.allPlayers {team := some (.exclude "")})) "Assigned")

@[mcfunction]
public def particleDynamic := input (g := Particle.grade {id := "minecraft:flame"}) fun n => do
  Particle.send {id := "minecraft:flame"} {count := .dynamic n}

@[mcfunction]
public def swingDynamic := input (g := Swing.grade .self) fun n => do
  Swing.run .self {duration := .ticks (.dynamic n)}

@[mcfunction]
public def scoreDynamic := input (g := Scoreboard.displayGrade) fun n => do
  Scoreboard.numberFormat (.one (.named "#bot")) points (.fixed (.number (.dynamic n)))

@[mcfunction]
public def particleNbt := capture (g := ⟨Req.dimension ||| Req.position,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.hud ||| Eff.failure⟩) do
  let data ← Nbt.literal (nbt% {color: [0.0, 1.0, 0.0], scale: 1.0})
  Particle.send {id := "minecraft:dust", options := .dynamic data}


end Oria.Proofs.Fixtures.Batch
