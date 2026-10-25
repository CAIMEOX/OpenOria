module
public import Oria.Proofs.Fixtures.Batch.Common
public meta import Oria.Proofs.Fixtures.Batch.Common

namespace Oria.Proofs.Fixtures.Batch
open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
public def creative := capture (GameMode.set .creative .self)

@[mcfunction]
public def survival := capture (GameMode.set .survival .self)

@[mcfunction]
public def xpLevels := capture (Experience.set .self (.static 3) .levels)

@[mcfunction]
public def xpPoints := capture (Experience.set .self (.static 5) .points)

@[mcfunction]
public def xpAdd := capture (Experience.add .self (.static 2) .points)

@[mcfunction]
public def xpQuery := capture (Experience.query .self .points)

@[mcfunction]
public def xpQueryLevels := capture (Experience.query .self .levels)

@[mcfunction]
public def xpTooMany := capture (Experience.set .self (.static 100000) .points)

@[mcfunction]
public def recipeGive := capture (Recipe.give .all (.one "batch:test"))

@[mcfunction]
public def recipeTake := capture (Recipe.take .all (.one "batch:test"))

@[mcfunction]
public def recipeAll := capture (Recipe.give .all .all)

@[mcfunction]
public def recipeTakeAll := capture (Recipe.take .all .all)

@[mcfunction]
public def enchant := capture (Enchant.apply .self "minecraft:sharpness" (.static 1))

@[mcfunction]
public def damage := capture (Damage.apply victim (.decimal 2.5))

@[mcfunction]
public def damageType := capture (Damage.apply victim (.static 2) (some (.type "minecraft:generic")))

@[mcfunction]
public def damageAt := capture (Damage.apply victim (.static 3) (some (.at "minecraft:generic" origin)))

@[mcfunction]
public def damageBy := capture (Damage.apply victim (.static 4) (some (.by "minecraft:generic" .self none)))

@[mcfunction]
public def damageFrom := capture (Damage.apply victim (.static 5) (some (.by "minecraft:generic" .self (some .self))))

@[mcfunction]
public def grantCriterion := capture (Advancement.grant .all (.only "batch:root" (some (.ofString "a"))))

@[mcfunction]
public def grantOnly := capture (Advancement.grant .all (.only "batch:root" none))

@[mcfunction]
public def grantFrom := capture (Advancement.grant .all (.from "batch:root"))

@[mcfunction]
public def grantUntil := capture (Advancement.grant .all (.until "batch:child"))

@[mcfunction]
public def grantThrough := capture (Advancement.grant .all (.through "batch:child"))

@[mcfunction]
public def grantEverything := capture (Advancement.grant .all .everything)

@[mcfunction]
public def revokeCriterion := capture (Advancement.revoke .all (.only "batch:root" (some (.ofString "a"))))

@[mcfunction]
public def revokeOnly := capture (Advancement.revoke .all (.only "batch:root" none))

@[mcfunction]
public def revokeFrom := capture (Advancement.revoke .all (.from "batch:root"))

@[mcfunction]
public def revokeUntil := capture (Advancement.revoke .all (.until "batch:child"))

@[mcfunction]
public def revokeThrough := capture (Advancement.revoke .all (.through "batch:child"))

@[mcfunction]
public def revokeEverything := capture (Advancement.revoke .all .everything)

end Oria.Proofs.Fixtures.Batch
