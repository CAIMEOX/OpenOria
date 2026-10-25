module
public import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Proofs.Fixtures.Batch.Common

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def barList := capture (Bossbar.list)

@[mcfunction]
public def barAdd := capture (Bossbar.add "batch:bar" (.literal "Round"))

@[mcfunction]
public def barRemove := capture (Bossbar.remove "batch:bar")

@[mcfunction]
public def barGetValue := capture (Bossbar.get "batch:bar" .value)

@[mcfunction]
public def barGetMax := capture (Bossbar.get "batch:bar" .max)

@[mcfunction]
public def barGetVisible := capture (Bossbar.get "batch:bar" .visible)

@[mcfunction]
public def barGetPlayers := capture (Bossbar.get "batch:bar" .players)

@[mcfunction]
public def barValue := capture (Bossbar.set "batch:bar" (.value (.static 5)))

@[mcfunction]
public def barMax := capture (Bossbar.set "batch:bar" (.max (.static 25)))

@[mcfunction]
public def barInvisible := capture (Bossbar.set "batch:bar" (.visible false))

@[mcfunction]
public def barVisible := capture (Bossbar.set "batch:bar" (.visible true))

@[mcfunction]
public def barColor := capture (Bossbar.set "batch:bar" (.color .red))

@[mcfunction]
public def barStyle := capture (Bossbar.set "batch:bar" (.style .notched_10))

@[mcfunction]
public def barName := capture (Bossbar.set "batch:bar" (.name (.literal "Changed")))

@[mcfunction]
public def barPlayers := capture (Bossbar.set "batch:bar" (.players (some .all)))

@[mcfunction]
public def barNoPlayers := capture (Bossbar.set "batch:bar" (.players none))

@[mcfunction]
public def teamList := capture (Team.list)

@[mcfunction]
public def teamAdd := capture (Team.add "batch.red")

@[mcfunction]
public def teamNamed := capture (Team.add "batch.blue" (some (.literal "Blue team")))

@[mcfunction]
public def teamJoin := capture (Team.join "batch.red" (.entities (.selector .allPlayers)))

@[mcfunction]
public def teamFake := capture (Team.join "batch.red" (.one (.named "#bot")))

@[mcfunction]
public def teamWildcard := capture (Team.join "batch.red" .all)

@[mcfunction]
public def teamSelf := capture (Team.join "batch.red")

@[mcfunction]
public def teamMembers := capture (Team.list (some "batch.red"))

@[mcfunction]
public def teamLeave := capture (Team.leave (.entities (.selector .allPlayers)))

@[mcfunction]
public def teamLeaveFake := capture (Team.leave (.one (.named "#bot")))

@[mcfunction]
public def teamEmpty := capture (Team.empty "batch.red")

@[mcfunction]
public def teamRemove := capture (Team.remove "batch.red")

@[mcfunction]
public def teamRemoveBlue := capture (Team.remove "batch.blue")

@[mcfunction]
public def teamColor := capture (Team.modify "batch.red" (.color (some .red)))

@[mcfunction]
public def teamResetColor := capture (Team.modify "batch.red" (.color none))

@[mcfunction]
public def teamFire := capture (Team.modify "batch.red" (.friendlyFire false))

@[mcfunction]
public def teamSight := capture (Team.modify "batch.red" (.seeFriendlyInvisibles false))

@[mcfunction]
public def teamName := capture (Team.modify "batch.red" (.displayName (.literal "Red team")))

@[mcfunction]
public def teamNameTags := capture (Team.modify "batch.red" (.nametagVisibility .hideForOtherTeams))

@[mcfunction]
public def teamDeathMessages := capture (Team.modify "batch.red" (.deathMessageVisibility .never))

@[mcfunction]
public def teamCollision := capture (Team.modify "batch.red" (.collisionRule .pushOwnTeam))

@[mcfunction]
public def teamPrefix := capture (Team.modify "batch.red" (.prefix (.literal "[R] ")))

@[mcfunction]
public def teamSuffix := capture (Team.modify "batch.red" (.suffix (.literal " !")))

end Oria.Proofs.Fixtures.Batch
