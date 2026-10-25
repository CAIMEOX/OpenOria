package oria.integration;

import net.minecraft.commands.CommandSourceStack;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.world.scores.ScoreHolder;
import net.minecraft.world.phys.Vec3;

/** Shared assertions for the bulk command fixtures. */
final class BatchAcceptance {
    static CommandSourceStack source(GameTestHelper t) {
        return t.getLevel().getServer().createCommandSourceStack().withLevel(t.getLevel())
            .withPosition(new Vec3(0, 64, 0));
    }

    static void set(GameTestHelper t, String holder, int value) {
        PlayerAcceptance.server(t, "scoreboard players set " + holder + " batch.points " + value);
    }

    static int score(GameTestHelper t, String holder) {
        var board = t.getLevel().getScoreboard();
        var value = board.getPlayerScoreInfo(ScoreHolder.forNameOnly(holder), board.getObjective("batch.points"));
        t.assertTrue(value != null, "missing batch score " + holder);
        return value.value();
    }

    static void invoke(GameTestHelper t, CommandSourceStack source, String name) {
        set(t, "#status", -1);
        PlayerAcceptance.command(t, source, "function batch:" + name.toLowerCase());
        PlayerAcceptance.clean(t, "batch");
    }

    static int ok(GameTestHelper t, CommandSourceStack source, String name) {
        invoke(t, source, name);
        t.assertTrue(score(t, "#status") == 1, name + " should succeed");
        return score(t, "#result");
    }

    static void result(GameTestHelper t, CommandSourceStack source, String name, int expected) {
        int value = ok(t, source, name);
        t.assertTrue(value == expected, name + " expected " + expected + ", got " + value);
    }

    static void fail(GameTestHelper t, CommandSourceStack source, String name) {
        invoke(t, source, name);
        t.assertTrue(score(t, "#status") == 0, name + " should fail");
    }
}
