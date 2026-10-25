package oria.integration;

import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.nbt.*;
import net.minecraft.network.chat.Component;
import net.minecraft.resources.Identifier;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.entity.EquipmentSlot;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.item.Items;
import net.minecraft.world.level.GameType;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.block.ChestBlock;
import net.minecraft.world.level.levelgen.Heightmap;
import net.minecraft.world.phys.Vec3;

import static oria.integration.BatchAcceptance.*;

/** Native context, selection, callback, and teleport semantics for the structured Execute API. */
final class ExecutionAcceptance {
    private static void probe(GameTestHelper t, CommandSourceStack s, String name, int expected) {
        set(t, "#hits", 0);
        invoke(t, s, name);
        t.assertTrue(score(t, "#hits") == expected, name + " expected " + expected +
            " branches, got " + score(t, "#hits"));
    }

    private static CompoundTag data(GameTestHelper t) {
        return t.getLevel().getServer().getCommandStorage().get(Identifier.parse("batch:execute"));
    }

    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var level = t.getLevel();
        var p = t.absolutePos(new BlockPos(2, 20, 2));
        level.getChunkAt(p);
        var s = source(t).withPosition(Vec3.atLowerCornerOf(p));
        set(t, "#one", 1);
        level.setBlockAndUpdate(p, Blocks.CHEST.defaultBlockState().setValue(ChestBlock.FACING, Direction.NORTH));
        var box = BlockContentAcceptance.chest(t, p);
        box.clearContent();
        probe(t, s, "execBlock", 1);
        probe(t, s, "execBlockNbt", 1);
        probe(t, s, "execSlots", 1);
        probe(t, s, "execNoSlots", 0);
        probe(t, s, "execItems", 0);
        box.setItem(0, new ItemStack(Items.APPLE, 3));
        probe(t, s, "execItems", 1);
        probe(t, s, "execBlockNbt", 0);
        level.setBlockAndUpdate(p.offset(1, 0, 0), Blocks.OAK_LOG.defaultBlockState());
        level.setBlockAndUpdate(p.offset(2, 0, 0), Blocks.AIR.defaultBlockState());
        level.setBlockAndUpdate(p.offset(4, 0, 0), Blocks.OAK_LOG.defaultBlockState());
        level.setBlockAndUpdate(p.offset(5, 0, 0), Blocks.AIR.defaultBlockState());
        probe(t, s, "execBlockTag", 1);
        probe(t, s, "execBlocks", 1);
        level.setBlockAndUpdate(p.offset(5, 0, 0), Blocks.STONE.defaultBlockState());
        probe(t, s, "execBlocks", 0);
        probe(t, s, "execMasked", 1);
        // BiomeManager samples neighboring quart cells; initialize the neighborhood.
        for (int dx : new int[]{-8, 8}) for (int dz : new int[]{-8, 8})
            level.getChunkAt(p.offset(dx, 0, dz));
        PlayerAcceptance.command(t, s, "fillbiome ~-8 ~-8 ~-8 ~8 ~8 ~8 minecraft:plains");
        t.assertTrue(level.getBiome(p).is(net.minecraft.world.level.biome.Biomes.PLAINS), "biome scene");
        probe(t, s, "execBiome", 1);
        probe(t, s, "execBiomeTag", 1);
        probe(t, s, "execDimension", 1);
        probe(t, s, "execOtherDimension", 0);
        // Compare the condition to the pinned server's readiness predicate at this tick.
        var chunk = level.getChunkSource().getChunkNow(p.getX() >> 4, p.getZ() >> 4);
        boolean ready = chunk != null &&
            chunk.getFullStatus() == net.minecraft.server.level.FullChunkStatus.ENTITY_TICKING &&
            level.areEntitiesLoaded(net.minecraft.world.level.ChunkPos.containing(p).pack());
        probe(t, s, "execLoaded", ready ? 1 : 0);
        probe(t, s, "execNotLoaded", 1);
        probe(t, s, "execPredicate", 1);
        probe(t, s, "execInlinePredicate", 1);
        probe(t, s, "execHeightmaps", 1);

        var actor = t.spawn(EntityTypes.MARKER, new BlockPos(2, 20, 2));
        actor.snapTo(p.getX() + 0.5, p.getY() + 0.5, p.getZ() + 0.5);
        actor.addTag("execution.actor");
        actor.addTag("batch.victim");
        actor.setCustomName(Component.literal("A \"quoted\" \\ name$"));
        actor.setYRot(179);
        actor.setXRot(0);
        var self = s.withEntity(actor);
        probe(t, self, "selectName", 1);
        probe(t, self, "selectOtherName", 0);
        probe(t, self, "selectRotation", 1);
        probe(t, self, "selectNbt", 1);
        probe(t, self, "selectPredicate", 1);
        probe(t, s, "selectBox", 1);
        probe(t, s.withPosition(Vec3.atLowerCornerOf(p.offset(8, 0, 0))), "selectBox", 0);
        ada.entity().setGameMode(GameType.ADVENTURE);
        bob.entity().setGameMode(GameType.CREATIVE);
        PlayerAcceptance.server(t, "experience set Ada 4 levels");
        probe(t, s, "selectMode", 1);
        probe(t, s, "selectNotMode", 1);
        ada.entity().snapTo(20, 70, 20);
        bob.entity().snapTo(30, 70, 30);
        probe(t, s, "selectOrigin", 1);
        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, new ItemStack(Items.APPLE, 1));
        probe(t, s.withEntity(ada.entity()), "execHands", 1);
        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, ItemStack.EMPTY);
        probe(t, s.withEntity(ada.entity()), "execHands", 0);
        PlayerAcceptance.server(t, "advancement revoke @a only batch:root");
        PlayerAcceptance.server(t, "advancement grant Ada only batch:root a");
        PlayerAcceptance.server(t, "advancement grant Bob only batch:root");
        probe(t, s, "selectAdvancement", 1);
        probe(t, s, "selectCompleted", 1);

        var vehicle = t.spawn(EntityTypes.PIG, new BlockPos(3, 20, 2));
        vehicle.addTag("execution.vehicle");
        PlayerAcceptance.command(t, self, "ride @s mount @e[tag=execution.vehicle,limit=1]");
        probe(t, self, "execVehicle", 1);
        probe(t, s.withEntity(vehicle), "execPassengers", 1);
        // Relation forms with no related entity yield no body invocation.
        for (var name : new String[]{"execOwner", "execController", "execLeasher",
                "execTarget", "execAttacker", "execOrigin"})
            probe(t, self, name, 0);
        PlayerAcceptance.command(t, self, "ride @s dismount");
        probe(t, self, "execVehicle", 0);
        invoke(t, s, "execSummon");
        PlayerAcceptance.command(t, s, "execute as @e[type=minecraft:marker,scores={batch.points=41}] run tag @s add execution.summoned");
        PlayerAcceptance.command(t, s, "execute if entity @e[tag=execution.summoned] run scoreboard players set #hits batch.points 73");
        t.assertTrue(score(t, "#hits") == 73, "summon supplies the spawned executor");
        invoke(t, s, "execHeight");
        t.assertTrue(actor.getY() == level.getHeight(Heightmap.Types.WORLD_SURFACE, p.getX(), p.getZ()),
            "positioned over uses heightmap position");

        PlayerAcceptance.server(t, "bossbar add batch:execute \"Execute\"");
        invoke(t, s, "execStoreNumbers");
        var stored = data(t);
        t.assertTrue(stored.get("b").equals(ByteTag.valueOf((byte)-3)), "byte store truncates after scale");
        t.assertTrue(stored.get("s").equals(ShortTag.valueOf((short)-3)), "short store");
        t.assertTrue(stored.get("i").equals(IntTag.valueOf(-3)), "int store");
        t.assertTrue(stored.get("l").equals(LongTag.valueOf(-3)), "long store");
        t.assertTrue(stored.get("f").equals(FloatTag.valueOf(-3.5f)), "float store");
        t.assertTrue(stored.get("d").equals(DoubleTag.valueOf(-3.5)), "double store");
        invoke(t, s, "execStoreZero");
        t.assertTrue(data(t).get("ok").equals(ByteTag.valueOf((byte)1)) &&
            data(t).get("result").equals(IntTag.valueOf(0)), "successful zero result");
        var bar = level.getServer().getCustomBossEvents().get(Identifier.parse("batch:execute"));
        t.assertTrue(bar.value() == 0 && bar.max() == 1, "bossbar result and success receivers");
        invoke(t, s, "execStoreFail");
        t.assertTrue(data(t).get("ok").equals(ByteTag.valueOf((byte)0)) &&
            data(t).get("result").equals(IntTag.valueOf(0)) && bar.value() == 0, "failure callbacks");
        PlayerAcceptance.server(t, "data modify storage batch:execute values set value [0,0,0]");
        set(t, "#input", 1);
        result(t, s, "execStoreDynamic", 1);
        t.assertTrue(data(t).getListOrEmpty("values").get(1).equals(IntTag.valueOf(2)), "dynamic store path");
        invoke(t, s, "execStoreEntity");
        t.assertTrue(actor.getAirSupply() == 123, "entity NBT receiver");
        level.setBlockAndUpdate(p, Blocks.HOPPER.defaultBlockState());
        invoke(t, s, "execStoreBlock");
        PlayerAcceptance.command(t, s, "execute store result score #check batch.points run data get block ~ ~ ~ TransferCooldown");
        t.assertTrue(score(t, "#check") == 12, "block NBT receiver");

        var first = t.spawn(EntityTypes.MARKER, new BlockPos(4, 20, 2));
        var second = t.spawn(EntityTypes.MARKER, new BlockPos(5, 20, 2));
        first.addTag("execution.child");
        second.addTag("execution.child");
        PlayerAcceptance.command(t, s, "scoreboard players set @e[tag=execution.child] batch.points 42");
        invoke(t, self, "execStoreFork");
        t.assertTrue(actor.getAirSupply() == 42 && first.getAirSupply() == 1 &&
            second.getAirSupply() == 1, "NBT receivers bind before or after fork at their chain position");

        var destination = t.spawn(EntityTypes.MARKER, new BlockPos(6, 20, 2));
        destination.addTag("execution.destination");
        destination.setYRot(45);
        destination.setXRot(15);
        result(t, s, "teleportEntity", 1);
        t.assertTrue(actor.position().equals(destination.position()) &&
            actor.getYRot() == 45 && actor.getXRot() == 15, "entity destination copies position and rotation");
        result(t, s, "teleportPlural", 2);
        t.assertTrue(first.position().equals(s.getPosition()) && first.getYRot() == 90.5f &&
            second.position().equals(s.getPosition()), "plural targets and fractional rotation");
        result(t, s, "teleportFacing", 1);
        t.assertTrue(Math.abs(actor.getYRot() + 90) < 0.01, "facing position");
        result(t, s, "teleportFacingEntity", 1);
        double facingYaw = Math.toDegrees(Math.atan2(destination.getZ() - actor.getZ(),
            destination.getX() - actor.getX())) - 90;
        t.assertTrue(Math.abs(actor.getYRot() - facingYaw) < 0.01, "facing entity");
        set(t, "#input", 20);
        result(t, s.withRotation(new net.minecraft.world.phys.Vec2(0, 30)), "teleportDynamic", 1);
        t.assertTrue(Math.abs(actor.getYRot() - 50) < 0.001,
            "dynamic angle relative to execution rotation, got " + actor.getYRot());
        destination.addTag("batch.victim");
        destination.removeTag("execution.destination");
        fail(t, s, "teleportEntity");

        actor.discard();
        vehicle.discard();
        first.discard();
        second.discard();
        destination.discard();
        PlayerAcceptance.command(t, s, "kill @e[tag=execution.summoned]");
        PlayerAcceptance.server(t, "bossbar remove batch:execute");
        PlayerAcceptance.server(t, "advancement revoke @a only batch:root");
        ada.entity().setGameMode(GameType.SURVIVAL);
        bob.entity().setGameMode(GameType.SURVIVAL);
        ada.entity().snapTo(0, 64, 0);
        bob.entity().snapTo(0, 64, 0);
    }
}
