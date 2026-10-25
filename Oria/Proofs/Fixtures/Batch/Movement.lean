module

public import Oria.Proofs.Fixtures.Batch.ControlCommon
public meta import Oria.Proofs.Fixtures.Batch.ControlCommon

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def respawnHere := capture (Spawnpoint.set)

@[mcfunction]
public def respawnAt := capture (Spawnpoint.set .all (.atPos blockOrigin none))

@[mcfunction]
public def respawnRotation := capture (Spawnpoint.set .all (.atPos blockOrigin (some ⟨.absolute (.decimal 450.0), .absolute (.decimal 120.0)⟩)))

@[mcfunction]
public def respawnLocal := capture (Spawnpoint.set .self (.atPos (.local (.static 0) (.static 0) (.static 1)) none))

@[mcfunction]
public def worldSpawnHere := capture (SetWorldSpawn.set)

@[mcfunction]
public def worldSpawnAt := capture (SetWorldSpawn.set (.atPos blockOrigin none))

@[mcfunction]
public def worldSpawnRotation := capture (SetWorldSpawn.set (.atPos blockOrigin (some ⟨.absolute (.static 30), .absolute (.static 15)⟩)))

@[mcfunction]
public def cameraStart := capture (Spectate.start rider)

@[mcfunction]
public def cameraStop := capture (Spectate.stop)

@[mcfunction]
public def mount := capture (Ride.mount rider vehicle)

@[mcfunction]
public def dismount := capture (Ride.dismount rider)

@[mcfunction]
public def mountCycle := capture (Ride.mount vehicle rider)

@[mcfunction]
public def rotateAngles := capture (Rotate.run rider (.angles ⟨.absolute (.static 90), .absolute (.static 10)⟩))

@[mcfunction]
public def rotateRelative := capture (Rotate.run rider (.angles ⟨.relative (.static 15), .relative (.static (-5))⟩))

@[mcfunction]
public def rotateFacing := capture (Rotate.run rider (.facing origin))

@[mcfunction]
public def rotateEntity := capture (Rotate.run rider (.entity vehicle .eyes))

@[mcfunction]
public def spreadOne := capture (SpreadPlayers.run rider ⟨.relative (.static 0), .relative (.static 0)⟩ {distance := .static 0, range := .static 2})

@[mcfunction]
public def spreadTeams := capture (SpreadPlayers.run (.selector .allPlayers) ⟨.relative (.static 0), .relative (.static 0)⟩ {distance := .static 1, range := .static 3, under := some (.static 100), respectTeams := true})

@[mcfunction]
public def rotationDynamic := input (g := Rotate.grade rider (.angles ⟨.absolute (.static 0), .absolute (.static 0)⟩)) fun n => do
  Rotate.run rider (.angles ⟨.absolute (.dynamic n), .absolute (.static 0)⟩)

@[mcfunction]
public def spawnDynamic := input (g := Spawnpoint.grade .all (.atPos blockOrigin none)) fun n => do
  Spawnpoint.set .all (.atPos (.world (.relative (.dynamic n)) (.relative (.static 0)) (.relative (.static 0))) none)

end Oria.Proofs.Fixtures.Batch
