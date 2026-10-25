package oria.integration;

import net.minecraft.core.BlockPos;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.level.GameType;
import net.minecraft.world.level.ChunkPos;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.gamerules.GameRules;
import net.minecraft.world.phys.Vec2;
import net.minecraft.world.phys.Vec3;

import static oria.integration.BatchAcceptance.*;

final class ControlAcceptance {
    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var s = source(t);
        var self = s.withEntity(ada.entity());
        var level = t.getLevel();
        var rules = level.getGameRules();
        var server = level.getServer();
        boolean keep = rules.get(GameRules.KEEP_INVENTORY);
        int speed = rules.get(GameRules.RANDOM_TICK_SPEED);
        rules.set(GameRules.KEEP_INVENTORY, false, server);
        result(t, s, "ruleRead", 0);
        result(t, s, "ruleOn", 1);
        fail(t, s, "ruleOn");
        result(t, s, "ruleRead", 1);
        result(t, s, "ruleOff", 0);
        set(t, "#input", 7);
        result(t, s, "ruleDynamic", 7);
        result(t, s, "ruleRandomRead", 7);
        set(t, "#input", -1);
        fail(t, s, "ruleDynamic");
        rules.set(GameRules.KEEP_INVENTORY, keep, server);
        rules.set(GameRules.RANDOM_TICK_SPEED, speed, server);

        // Isolate loading-ticket changes from the overworld entity acceptance scene.
        var forceLevel = server.getLevel(net.minecraft.world.level.Level.NETHER);
        var forceSource = s.withLevel(forceLevel);
        long[] forced = forceLevel.getForceLoadedChunks().toLongArray();
        result(t, forceSource, "loadClear", 0);
        result(t, forceSource, "loadList", 0);
        result(t, forceSource, "loadAdd", 1);
        fail(t, forceSource, "loadAdd");
        result(t, forceSource, "loadQuery", 1);
        result(t, forceSource, "loadRange", 1);
        result(t, forceSource, "loadList", 2);
        t.assertTrue(forceLevel.getForceLoadedChunks().contains(ChunkPos.pack(0, 0)) &&
            forceLevel.getForceLoadedChunks().contains(ChunkPos.pack(1, 0)), "block coordinates select chunks");
        result(t, forceSource, "loadRemove", 1);
        fail(t, forceSource, "loadQuery");
        result(t, forceSource, "loadRemoveRange", 1);
        set(t, "#input", 16 * 256);
        fail(t, forceSource, "loadDynamic");
        result(t, forceSource, "loadClear", 0);
        for (long pos : forced) forceLevel.setChunkForced(ChunkPos.getX(pos), ChunkPos.getZ(pos), true);

        var rider = t.spawn(EntityTypes.PIG, new BlockPos(2, 3, 2));
        var vehicle = t.spawn(EntityTypes.COW, new BlockPos(3, 3, 3));
        var marker = t.spawn(EntityTypes.MARKER, new BlockPos(4, 3, 3));
        rider.addTag("control.rider");
        vehicle.addTag("control.vehicle");
        marker.addTag("control.marker");
        int initial = ok(t, s, "attrBase");
        result(t, s, "attrSet", 1);
        result(t, s, "attrBase", 165);
        result(t, s, "attrAdd", 1);
        fail(t, s, "attrAdd");
        result(t, s, "attrGet", 185);
        result(t, s, "attrMultiplyBase", 1);
        result(t, s, "attrGet", 277);
        result(t, s, "attrNegative", -277);
        result(t, s, "attrModifier", 50);
        result(t, s, "attrMultiplyTotal", 1);
        result(t, s, "attrGet", 555);
        result(t, s, "attrRemove", 1);
        fail(t, s, "attrRemove");
        result(t, s, "attrRemoveBase", 1);
        result(t, s, "attrRemoveTotal", 1);
        result(t, s, "attrReset", 1);
        result(t, s, "attrBase", initial);
        fail(t, s, "attrMissing");
        set(t, "#input", 18);
        result(t, s, "attrDynamic", 1);
        result(t, s, "attrGet", 180);
        result(t, s, "mount", 1);
        t.assertTrue(rider.getVehicle() == vehicle, "riding relation established");
        fail(t, s, "mount");
        fail(t, s, "mountCycle");
        result(t, s, "dismount", 1);
        t.assertTrue(rider.getVehicle() == null, "riding relation removed");
        fail(t, s, "dismount");

        result(t, s, "rotateAngles", 1);
        t.assertTrue(rider.getYRot() == 90 && rider.getXRot() == 10, "absolute rotation");
        result(t, s.withRotation(new Vec2(20, 30)), "rotateRelative", 1);
        t.assertTrue(rider.getYRot() == 45 && rider.getXRot() == 15, "rotation reads command context");
        result(t, s, "rotateFacing", 1);
        result(t, s, "rotateEntity", 1);
        set(t, "#input", 120);
        result(t, s, "rotationDynamic", 1);
        t.assertTrue(rider.getYRot() == 120, "dynamic rotation");

        var mode = ada.entity().gameMode();
        fail(t, self, "cameraStart");
        ada.entity().setGameMode(GameType.SPECTATOR);
        result(t, self, "cameraStart", 1);
        t.assertTrue(ada.entity().getCamera() == rider, "spectator target");
        result(t, self, "cameraStop", 1);
        t.assertTrue(ada.entity().getCamera() == ada.entity(), "spectator reset");
        ada.entity().setGameMode(mode);

        var oldWorldSpawn = level.getRespawnData();
        var oldAdaSpawn = ada.entity().getRespawnConfig();
        var oldBobSpawn = bob.entity().getRespawnConfig();
        result(t, self, "respawnHere", 1);
        result(t, s, "respawnAt", 2);
        t.assertTrue(ada.entity().getRespawnConfig().respawnData().pos().equals(new BlockPos(0, 64, 0)),
            "player spawn uses command position");
        result(t, s, "respawnRotation", 2);
        var spawn = ada.entity().getRespawnConfig().respawnData();
        t.assertTrue(spawn.yaw() == 90 && spawn.pitch() == 90, "spawn rotation wraps and clamps");
        result(t, self, "respawnLocal", 1);
        set(t, "#input", 2);
        result(t, s, "spawnDynamic", 2);
        t.assertTrue(ada.entity().getRespawnConfig().respawnData().pos().getX() == 2, "dynamic block offset");
        result(t, s, "worldSpawnHere", 1);
        result(t, s, "worldSpawnAt", 1);
        result(t, s, "worldSpawnRotation", 1);
        t.assertTrue(level.getRespawnData().yaw() == 30 && level.getRespawnData().pitch() == 15,
            "world spawn rotation");
        level.setRespawnData(oldWorldSpawn);
        ada.entity().setRespawnPosition(oldAdaSpawn, false);
        bob.entity().setRespawnPosition(oldBobSpawn, false);

        var center = t.absolutePos(new BlockPos(24, 3, 24));
        for (int x = 18; x <= 30; ++x) for (int z = 18; z <= 30; ++z) {
            t.setBlock(new BlockPos(x, 1, z), Blocks.STONE);
            for (int y = 2; y <= 6; ++y) t.setBlock(new BlockPos(x, y, z), Blocks.AIR);
        }
        var spread = s.withPosition(Vec3.atCenterOf(center));
        result(t, spread, "spreadOne", 1);
        t.assertTrue(Math.abs(rider.getX() - spread.getPosition().x) <= 3 &&
            Math.abs(rider.getZ() - spread.getPosition().z) <= 3, "spread within range");
        var board = level.getScoreboard();
        var team = board.addPlayerTeam("control.spread");
        board.addPlayerToTeam(ada.entity().getScoreboardName(), team);
        result(t, spread, "spreadTeams", 2);
        board.removePlayerTeam(team);
        ada.entity().snapTo(0, 64, 0);
        bob.entity().snapTo(0, 64, 0);
        DisplayControlAcceptance.run(t, ada, bob);
        rider.discard();
        vehicle.discard();
        marker.discard();
    }
}
