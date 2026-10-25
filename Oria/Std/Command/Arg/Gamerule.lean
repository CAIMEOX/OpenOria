module

public import Oria.Std.Command.Arg

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Typed game rules

The pinned DP121 registry supplies Boolean and integer rules. Each descriptor fixes the
accepted host argument type; integer rules accept Scalar for runtime I32 inputs. Minecraft
checks each rule's numeric bounds. Native rule names are short registry names.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode ArgCodec)

/-- A native game rule with its assignment type fixed by the registry. -/
public structure GameRule (a : Type) where
  private mk ::
  /-- Native command name. -/
  name : Oria.Command.Word

/-- A typed rule assignment encoded as one command argument. -/
public structure RuleUpdate where
  private mk ::
  /-- Native name and value fragments. -/
  fragment : Oria.Command.Fragment EncodedVal

/-- Form an assignment, checking the value type against its rule. -/
@[expose] public def GameRule.assign {a : Type} [ArgCodec a] (rule : GameRule a) (value : a) : RuleUpdate :=
  private_decl% (⟨.spaced [(encode rule.name).fragment, (encode value).fragment]⟩)

public instance : ArgCodec RuleUpdate where
  key := ⟨`minecraft.argument.rule_update⟩
  encode update := update.fragment

/-- Context requirements of an assignment. -/
@[expose] public def RuleUpdate.requirements (u : RuleUpdate) : ReqRow := (encode u).requirements

/-- Rule names add no context requirement; assignment preserves the value encoder's contract. -/
@[simp] public theorem GameRule.assign_requirements {a : Type} [ArgCodec a]
    (rule : GameRule a) (value : a) :
    (rule.assign value).requirements = (encode value).requirements := private_decl% (by
  change (Req.none ||| Req.none) ||| (encode value).requirements = _
  simp [Req.none])

namespace GameRule

/-- Native advance time rule. -/
@[expose] public def advanceTime : GameRule Bool := private_decl% (⟨"advance_time"⟩)

/-- Native advance weather rule. -/
@[expose] public def advanceWeather : GameRule Bool := private_decl% (⟨"advance_weather"⟩)

/-- Native allow entering nether using portals rule. -/
@[expose] public def allowEnteringNetherUsingPortals : GameRule Bool := private_decl% (⟨"allow_entering_nether_using_portals"⟩)

/-- Native block drops rule. -/
@[expose] public def blockDrops : GameRule Bool := private_decl% (⟨"block_drops"⟩)

/-- Native block explosion drop decay rule. -/
@[expose] public def blockExplosionDropDecay : GameRule Bool := private_decl% (⟨"block_explosion_drop_decay"⟩)

/-- Native command blocks work rule. -/
@[expose] public def commandBlocksWork : GameRule Bool := private_decl% (⟨"command_blocks_work"⟩)

/-- Native command block output rule. -/
@[expose] public def commandBlockOutput : GameRule Bool := private_decl% (⟨"command_block_output"⟩)

/-- Native drowning damage rule. -/
@[expose] public def drowningDamage : GameRule Bool := private_decl% (⟨"drowning_damage"⟩)

/-- Native elytra movement check rule. -/
@[expose] public def elytraMovementCheck : GameRule Bool := private_decl% (⟨"elytra_movement_check"⟩)

/-- Native ender pearls vanish on death rule. -/
@[expose] public def enderPearlsVanishOnDeath : GameRule Bool := private_decl% (⟨"ender_pearls_vanish_on_death"⟩)

/-- Native entity drops rule. -/
@[expose] public def entityDrops : GameRule Bool := private_decl% (⟨"entity_drops"⟩)

/-- Native fall damage rule. -/
@[expose] public def fallDamage : GameRule Bool := private_decl% (⟨"fall_damage"⟩)

/-- Native fire damage rule. -/
@[expose] public def fireDamage : GameRule Bool := private_decl% (⟨"fire_damage"⟩)

/-- Native fire spread radius around player rule. -/
@[expose] public def fireSpreadRadiusAroundPlayer : GameRule Scalar := private_decl% (⟨"fire_spread_radius_around_player"⟩)

/-- Native forgive dead players rule. -/
@[expose] public def forgiveDeadPlayers : GameRule Bool := private_decl% (⟨"forgive_dead_players"⟩)

/-- Native freeze damage rule. -/
@[expose] public def freezeDamage : GameRule Bool := private_decl% (⟨"freeze_damage"⟩)

/-- Native global sound events rule. -/
@[expose] public def globalSoundEvents : GameRule Bool := private_decl% (⟨"global_sound_events"⟩)

/-- Native immediate respawn rule. -/
@[expose] public def immediateRespawn : GameRule Bool := private_decl% (⟨"immediate_respawn"⟩)

/-- Native keep inventory rule. -/
@[expose] public def keepInventory : GameRule Bool := private_decl% (⟨"keep_inventory"⟩)

/-- Native lava source conversion rule. -/
@[expose] public def lavaSourceConversion : GameRule Bool := private_decl% (⟨"lava_source_conversion"⟩)

/-- Native limited crafting rule. -/
@[expose] public def limitedCrafting : GameRule Bool := private_decl% (⟨"limited_crafting"⟩)

/-- Native locator bar rule. -/
@[expose] public def locatorBar : GameRule Bool := private_decl% (⟨"locator_bar"⟩)

/-- Native log admin commands rule. -/
@[expose] public def logAdminCommands : GameRule Bool := private_decl% (⟨"log_admin_commands"⟩)

/-- Native max block modifications rule. -/
@[expose] public def maxBlockModifications : GameRule Scalar := private_decl% (⟨"max_block_modifications"⟩)

/-- Native max command forks rule. -/
@[expose] public def maxCommandForks : GameRule Scalar := private_decl% (⟨"max_command_forks"⟩)

/-- Native max command sequence length rule. -/
@[expose] public def maxCommandSequenceLength : GameRule Scalar := private_decl% (⟨"max_command_sequence_length"⟩)

/-- Native max entity cramming rule. -/
@[expose] public def maxEntityCramming : GameRule Scalar := private_decl% (⟨"max_entity_cramming"⟩)

/-- Native max minecart speed rule. -/
@[expose] public def maxMinecartSpeed : GameRule Scalar := private_decl% (⟨"max_minecart_speed"⟩)

/-- Native max snow accumulation height rule. -/
@[expose] public def maxSnowAccumulationHeight : GameRule Scalar := private_decl% (⟨"max_snow_accumulation_height"⟩)

/-- Native mob drops rule. -/
@[expose] public def mobDrops : GameRule Bool := private_decl% (⟨"mob_drops"⟩)

/-- Native mob explosion drop decay rule. -/
@[expose] public def mobExplosionDropDecay : GameRule Bool := private_decl% (⟨"mob_explosion_drop_decay"⟩)

/-- Native mob griefing rule. -/
@[expose] public def mobGriefing : GameRule Bool := private_decl% (⟨"mob_griefing"⟩)

/-- Native natural health regeneration rule. -/
@[expose] public def naturalHealthRegeneration : GameRule Bool := private_decl% (⟨"natural_health_regeneration"⟩)

/-- Native player movement check rule. -/
@[expose] public def playerMovementCheck : GameRule Bool := private_decl% (⟨"player_movement_check"⟩)

/-- Native players nether portal creative delay rule. -/
@[expose] public def playersNetherPortalCreativeDelay : GameRule Scalar := private_decl% (⟨"players_nether_portal_creative_delay"⟩)

/-- Native players nether portal default delay rule. -/
@[expose] public def playersNetherPortalDefaultDelay : GameRule Scalar := private_decl% (⟨"players_nether_portal_default_delay"⟩)

/-- Native players sleeping percentage rule. -/
@[expose] public def playersSleepingPercentage : GameRule Scalar := private_decl% (⟨"players_sleeping_percentage"⟩)

/-- Native projectiles can break blocks rule. -/
@[expose] public def projectilesCanBreakBlocks : GameRule Bool := private_decl% (⟨"projectiles_can_break_blocks"⟩)

/-- Native pvp rule. -/
@[expose] public def pvp : GameRule Bool := private_decl% (⟨"pvp"⟩)

/-- Native raids rule. -/
@[expose] public def raids : GameRule Bool := private_decl% (⟨"raids"⟩)

/-- Native random tick speed rule. -/
@[expose] public def randomTickSpeed : GameRule Scalar := private_decl% (⟨"random_tick_speed"⟩)

/-- Native reduced debug info rule. -/
@[expose] public def reducedDebugInfo : GameRule Bool := private_decl% (⟨"reduced_debug_info"⟩)

/-- Native respawn radius rule. -/
@[expose] public def respawnRadius : GameRule Scalar := private_decl% (⟨"respawn_radius"⟩)

/-- Native send command feedback rule. -/
@[expose] public def sendCommandFeedback : GameRule Bool := private_decl% (⟨"send_command_feedback"⟩)

/-- Native show advancement messages rule. -/
@[expose] public def showAdvancementMessages : GameRule Bool := private_decl% (⟨"show_advancement_messages"⟩)

/-- Native show death messages rule. -/
@[expose] public def showDeathMessages : GameRule Bool := private_decl% (⟨"show_death_messages"⟩)

/-- Native spawner blocks work rule. -/
@[expose] public def spawnerBlocksWork : GameRule Bool := private_decl% (⟨"spawner_blocks_work"⟩)

/-- Native spawn mobs rule. -/
@[expose] public def spawnMobs : GameRule Bool := private_decl% (⟨"spawn_mobs"⟩)

/-- Native spawn monsters rule. -/
@[expose] public def spawnMonsters : GameRule Bool := private_decl% (⟨"spawn_monsters"⟩)

/-- Native spawn patrols rule. -/
@[expose] public def spawnPatrols : GameRule Bool := private_decl% (⟨"spawn_patrols"⟩)

/-- Native spawn phantoms rule. -/
@[expose] public def spawnPhantoms : GameRule Bool := private_decl% (⟨"spawn_phantoms"⟩)

/-- Native spawn wandering traders rule. -/
@[expose] public def spawnWanderingTraders : GameRule Bool := private_decl% (⟨"spawn_wandering_traders"⟩)

/-- Native spawn wardens rule. -/
@[expose] public def spawnWardens : GameRule Bool := private_decl% (⟨"spawn_wardens"⟩)

/-- Native spectators generate chunks rule. -/
@[expose] public def spectatorsGenerateChunks : GameRule Bool := private_decl% (⟨"spectators_generate_chunks"⟩)

/-- Native spread vines rule. -/
@[expose] public def spreadVines : GameRule Bool := private_decl% (⟨"spread_vines"⟩)

/-- Native tnt explodes rule. -/
@[expose] public def tntExplodes : GameRule Bool := private_decl% (⟨"tnt_explodes"⟩)

/-- Native tnt explosion drop decay rule. -/
@[expose] public def tntExplosionDropDecay : GameRule Bool := private_decl% (⟨"tnt_explosion_drop_decay"⟩)

/-- Native universal anger rule. -/
@[expose] public def universalAnger : GameRule Bool := private_decl% (⟨"universal_anger"⟩)

/-- Native water source conversion rule. -/
@[expose] public def waterSourceConversion : GameRule Bool := private_decl% (⟨"water_source_conversion"⟩)

end GameRule
end Oria.Std.Command.Arg
