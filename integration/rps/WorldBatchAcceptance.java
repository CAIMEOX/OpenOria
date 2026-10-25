package oria.integration;

import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.world.Difficulty;
import net.minecraft.world.level.GameType;

import static oria.integration.BatchAcceptance.*;

/** World-state contracts in an isolated world, resetting shared gameplay settings afterward. */
final class WorldBatchAcceptance {
    static void run(GameTestHelper t) {
        var s = source(t);
        var server = t.getLevel().getServer();
        var level = t.getLevel();
        var oldDifficulty = level.getDifficulty();
        var oldMode = server.getDefaultGameType();
        result(t, s, "weatherClear", 200);
        t.assertFalse(server.getWeatherData().isRaining(), "clear weather");
        result(t, s, "weatherRain", 100);
        t.assertTrue(server.getWeatherData().isRaining(), "rain weather");
        result(t, s, "weatherThunder", 300);
        t.assertTrue(server.getWeatherData().isThundering(), "thunder weather");
        result(t, s, "weatherSample", -1);
        set(t, "#input", 75);
        result(t, s, "weatherDynamic", 75);
        set(t, "#input", 0);
        fail(t, s, "weatherDynamic");
        ok(t, s, "weatherClear");

        invoke(t, s, "clockResume");
        result(t, s, "clockPause", 1);
        fail(t, s, "clockPause");
        result(t, s, "clockSet", 6000);
        result(t, s, "clockQuery", 6000);
        result(t, s, "clockDefault", 6000);
        fail(t, s, "clockSet");
        result(t, s, "clockAdd", 5900);
        result(t, s, "clockQuery", 5900);
        result(t, s, "timelineTicks", 5900);
        result(t, s, "timelineRepetition", 0);
        result(t, s, "clockRate", 1);
        fail(t, s, "clockRate");
        set(t, "#input", 26000);
        result(t, s, "clockDynamic", 26000);
        result(t, s, "timelineTicks", 2000);
        result(t, s, "timelineRepetition", 1);
        ok(t, s, "clockMarker");
        ok(t, s, "gameTime");
        ok(t, s, "clockResetRate");
        ok(t, s, "clockResume");

        result(t, s, "difficultyGet", oldDifficulty.getId());
        if (oldDifficulty == Difficulty.HARD) server.setDifficulty(Difficulty.NORMAL, true);
        result(t, s, "difficultySet", 0);
        result(t, s, "difficultyGet", Difficulty.HARD.getId());
        fail(t, s, "difficultySet");
        server.setDifficulty(oldDifficulty, true);
        ok(t, s, "defaultMode");
        t.assertTrue(server.getDefaultGameType() == GameType.ADVENTURE, "default game mode");
        server.setDefaultGameType(oldMode);

        var b = level.getWorldBorder();
        double size = b.getSize(), x = b.getCenterX(), z = b.getCenterZ();
        double safe = b.getSafeZone(), damage = b.getDamagePerBlock();
        int warningTime = b.getWarningTime(), warningBlocks = b.getWarningBlocks();
        ok(t, s, "borderSet");
        result(t, s, "borderGet", 1000);
        fail(t, s, "borderSet");
        ok(t, s, "borderAdd");
        result(t, s, "borderGet", 1100);
        ok(t, s, "borderCenter");
        t.assertTrue(b.getCenterX() == 10.5 && b.getCenterZ() == 20.5, "border fractional center");
        fail(t, s, "borderCenter");
        ok(t, s, "borderBuffer");
        ok(t, s, "borderDamage");
        ok(t, s, "borderWarningDistance");
        ok(t, s, "borderWarningTime");
        t.assertTrue(b.getSafeZone() == 7.5 && b.getDamagePerBlock() == 0.25 &&
            b.getWarningBlocks() == 9 && b.getWarningTime() == 40, "border settings and time units");
        set(t, "#input", 900);
        ok(t, s, "borderDynamic");
        result(t, s, "borderGet", 900);
        set(t, "#input", -1);
        fail(t, s, "borderDynamic");
        ok(t, s, "borderTransition");
        t.assertTrue(b.getLerpTarget() == 1200 && b.getLerpTime() > 0, "border transition");
        b.setSize(size);
        b.setCenter(x, z);
        b.setSafeZone(safe);
        b.setDamagePerBlock(damage);
        b.setWarningTime(warningTime);
        b.setWarningBlocks(warningBlocks);
    }
}
