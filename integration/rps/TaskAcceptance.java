package oria.integration;

import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.gametest.framework.TestFunctionLoader;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.level.gamerules.GameRules;
import net.minecraft.world.scores.ScoreHolder;

/** Exercise resumable calls through the generated datapacks and the server's own quota. */
public final class TaskAcceptance {
    public static void main(String[] args) throws Exception {
        TestFunctionLoader.registerLoader(registrar -> registrar.accept(
            ResourceKey.create(Registries.TEST_FUNCTION, Identifier.parse("rps_test:game")), TaskAcceptance::run));
        net.minecraft.gametest.Main.main(args);
    }

    private static int get(GameTestHelper t, String holder, String objective) {
        var board = t.getLevel().getScoreboard();
        var value = board.getPlayerScoreInfo(ScoreHolder.forNameOnly(holder), board.getObjective(objective));
        return value == null ? 0 : value.value();
    }

    private static void invoke(GameTestHelper t, String ns, String function) {
        PlayerAcceptance.server(t, "function " + ns + ":" + function);
    }

    private static void run(GameTestHelper t) {
        t.getLevel().getGameRules().set(GameRules.MAX_COMMAND_SEQUENCE_LENGTH, 512, t.getLevel().getServer());
        var variants = new String[]{"task_test", "task_stack"};
        var variant = new int[]{0};
        var phase = new int[]{0};
        var launched = new boolean[]{false};
        t.onEachTick(() -> {
            String ns = variants[variant[0]];
            String vm = ns + ".oria";
            t.assertTrue(get(t, "#phase", vm) == 0,
                "a task slice or ordinary entry retained the execution phase");
            if (!launched[0]) {
                PlayerAcceptance.server(t, "scoreboard players set #input task.points 3");
                PlayerAcceptance.server(t, "scoreboard players set #noise task.points 0");
                PlayerAcceptance.server(t, "scoreboard players set #effects task.points 0");
                invoke(t, ns, "start");
                PlayerAcceptance.server(t, "execute store success score #busy task.points run function " + ns + ":alias");
                t.assertTrue(get(t, "#busy", "task.points") == 0, "busy task was overwritten");
                launched[0] = true;
            }
            if (get(t, "#task.phase", vm) != 0) {
                invoke(t, ns, "clobber");
                PlayerAcceptance.server(t, "execute store success score #gc task.points run function " + ns + ":gc");
                t.assertTrue(get(t, "#gc", "task.points") == 0, "collector ran while a task retained pointers");
                return;
            }
            int status = get(t, "#task.status", vm);
            if (phase[0] == 0) {
                t.assertTrue(status == 2, "work task failed with status " + status);
                t.assertTrue(get(t, "#answer", "task.points") == 873, "resumed computation lost a local or arena object");
                t.assertTrue(get(t, "#effects", "task.points") == 40, "effects were repeated or skipped");
                t.assertTrue(get(t, "#pair", "task.points") == 21, "multiword return lost a component");
                t.assertTrue(get(t, "#tail", "task.points") == 210, "tail backedge lost its loop state");
                t.assertTrue(get(t, "#task.slices", vm) > 1, "long computation did not cross ticks");
                t.assertTrue(get(t, "#task.parks", vm) > 1, "fuel did not trigger cooperative parking");
                invoke(t, ns, "snapshot");
                t.assertTrue(get(t, "#root", "task.points") == 873, "persistent result was not published");
                invoke(t, ns, "gc");
                invoke(t, ns, "recovery");
                phase[0] = 1;
            } else if (phase[0] == 1) {
                t.assertTrue(status == 2 && get(t, "#caught", "task.points") == -7,
                    "failure handler: status=" + status + ", caught=" + get(t, "#caught", "task.points") +
                    ", slices=" + get(t, "#task.slices", vm));
                invoke(t, ns, "fail");
                phase[0] = 2;
            } else if (phase[0] == 2) {
                t.assertTrue(status == 3, "unhandled failure did not complete the task");
                invoke(t, ns, "plain");
                phase[0] = 3;
            } else if (phase[0] == 3) {
                t.assertTrue(status == 2 && get(t, "#plain", "task.points") == 1,
                    "atomic background entry failed");
                invoke(t, ns, "alias");
                PlayerAcceptance.server(t, "execute store success score #cancel task.points run function " + ns + ":recovery/cancel");
                t.assertTrue(get(t, "#cancel", "task.points") == 0, "another entry cancelled the active task");
                invoke(t, ns, "start/cancel");
                t.assertTrue(get(t, "#task.status", vm) == 5 && get(t, "#task.phase", vm) == 0,
                    "cancellation did not release the task slot");
                var data = t.getLevel().getServer().getCommandStorage().get(Identifier.parse(ns + ".task:runtime"));
                t.assertTrue(!data.contains("arena") && !data.contains("stack"), "cancelled task retained its workspace");
                PlayerAcceptance.server(t, "scoreboard players set #plain task.points 0");
                invoke(t, ns, "plain");
                phase[0] = 4;
            } else if (phase[0] == 4) {
                t.assertTrue(status == 2 && get(t, "#plain", "task.points") == 1,
                    "replacement task did not resume after cancellation");
                t.assertTrue(get(t, "#effects", "task.points") == 40, "cancelled continuation executed an effect");
                t.getLevel().getGameRules().set(GameRules.MAX_COMMAND_SEQUENCE_LENGTH, 64, t.getLevel().getServer());
                invoke(t, ns, "start");
                phase[0] = 5;
            } else {
                t.assertTrue(status == 4, "insufficient server quota was repeatedly rescheduled");
                var data = t.getLevel().getServer().getCommandStorage().get(Identifier.parse(ns + ".task:runtime"));
                t.assertTrue(!data.contains("arena") && !data.contains("stack"), "task workspace survived completion");
                t.getLevel().getGameRules().set(GameRules.MAX_COMMAND_SEQUENCE_LENGTH, 512, t.getLevel().getServer());
                if (++variant[0] == variants.length) t.succeed();
                else {
                    phase[0] = 0;
                    launched[0] = false;
                }
            }
        });
    }
}
