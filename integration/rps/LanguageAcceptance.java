package oria.integration;

import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.gametest.framework.TestFunctionLoader;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.scores.ScoreHolder;

/** Observe language behavior through generated public datapack entries. */
public final class LanguageAcceptance {
    public static void main(String[] args) throws Exception {
        TestFunctionLoader.registerLoader(registrar -> registrar.accept(
            ResourceKey.create(Registries.TEST_FUNCTION, Identifier.parse("rps_test:game")),
            LanguageAcceptance::run));
        net.minecraft.gametest.Main.main(args);
    }

    private static void score(GameTestHelper t, String name, int expected) {
        PlayerAcceptance.score(t, ScoreHolder.forNameOnly(name), "ledger.points", expected);
    }

    private static void set(GameTestHelper t, String name, int value) {
        PlayerAcceptance.server(t, "scoreboard players set " + name + " ledger.points " + value);
    }

    private static void absent(GameTestHelper t, String name) {
        var board = t.getLevel().getScoreboard();
        t.assertTrue(board.getPlayerScoreInfo(ScoreHolder.forNameOnly(name),
            board.getObjective("ledger.points")) == null, "expected absent score " + name);
    }

    private static void invoke(GameTestHelper t, CommandSourceStack source, String ns, String path) {
        set(t, "#status", -1);
        set(t, "#result", -1);
        PlayerAcceptance.command(t, source, "function " + ns + ":" + path);
        PlayerAcceptance.clean(t, ns);
    }

    private static void records(GameTestHelper t, CommandSourceStack source, String ns) {
        set(t, "#old", -1);
        set(t, "#new", -1);
        invoke(t, source, ns, "records");
        score(t, "#old", 235);
        score(t, "#new", 336);
    }

    private static void snapshot(GameTestHelper t, CommandSourceStack source, String ns, int total) {
        set(t, "#total", -1);
        invoke(t, source, ns, "snapshot");
        score(t, "#total", total);
    }

    private static void round(GameTestHelper t, CommandSourceStack source, String ns,
            int input, int result, int visits) {
        set(t, "#input", input);
        invoke(t, source, ns, "round");
        score(t, "#status", 1);
        score(t, "#result", result);
        score(t, "#visits", visits);
        snapshot(t, source, ns, result);
    }

    private static void ledger(GameTestHelper t, CommandSourceStack source, String ns) {
        snapshot(t, source, ns, 0);
        invoke(t, source, ns, "reset");
        snapshot(t, source, ns, 0);
        set(t, "#visits", 0);
        round(t, source, ns, 1, 101, 1);
        round(t, source, ns, 2, 112, 2);
        round(t, source, ns, 0, 113, 3);

        // Command failure and source-level rejection both end the fallible computation.
        for (boolean missing : new boolean[]{false, true}) {
            if (missing) PlayerAcceptance.server(t, "scoreboard players reset #input ledger.points");
            else set(t, "#input", -7);
            invoke(t, source, ns, "round");
            score(t, "#status", 0);
            score(t, "#result", -999);
            score(t, "#visits", 3);
            snapshot(t, source, ns, 113);
        }

        set(t, "#old", -1);
        set(t, "#new", -1);
        invoke(t, source, ns, "durable-records");
        score(t, "#old", 113);
        score(t, "#new", 214);
        invoke(t, source, ns, "gc");
        snapshot(t, source, ns, 214);
        round(t, source, ns, 2, 225, 4);

        // Effects before a later command failure remain visible.
        set(t, "#input", 1);
        PlayerAcceptance.server(t, "scoreboard players reset #visits ledger.points");
        invoke(t, source, ns, "round");
        score(t, "#status", 0);
        score(t, "#result", -999);
        absent(t, "#visits");
        invoke(t, source, ns, "gc");
        snapshot(t, source, ns, 326);
    }

    private static void result(GameTestHelper t, CommandSourceStack source, String ns, String entry,
            int input, int result, int trace) {
        set(t, "#input", input);
        set(t, "#trace", 0);
        invoke(t, source, ns, entry);
        score(t, "#status", 1);
        score(t, "#result", result);
        score(t, "#trace", trace);
    }

    private static void control(GameTestHelper t, CommandSourceStack source, String ns) {
        result(t, source, ns, "control", -2, -10, 1);
        result(t, source, ns, "control", 0, 7, 124);
        result(t, source, ns, "control", 3, 10, 134);
        result(t, source, ns, "selection", 0, 0, 125);
        result(t, source, ns, "selection", 1, 1, 135);
        result(t, source, ns, "selection", 8, 8, 145);
        result(t, source, ns, "selection", -1, -11, 1);
        result(t, source, ns, "nested", -1, -2, 6);
        result(t, source, ns, "nested", 3, 5, 26);
        result(t, source, ns, "loop-control", 0, 0, 1349);
        result(t, source, ns, "loop-control", 3, 3, 19);
        result(t, source, ns, "loop-control", 1, 1, 9);
        result(t, source, ns, "loop-return", 0, 0, 12349);
        result(t, source, ns, "loop-return", 2, 12, 1);
        result(t, source, ns, "loop-return", 1, 11, 0);
        result(t, source, ns, "collections", 0, 0, 1234);
        set(t, "#native", -1);
        result(t, source, ns, "native-loop", 0, 7, 0);
        score(t, "#native", 3);

        // A failed branch has already emitted its prefix. Its suffix does not run.
        PlayerAcceptance.server(t, "scoreboard players reset #unavailable ledger.points");
        set(t, "#input", 99);
        set(t, "#trace", 0);
        invoke(t, source, ns, "control");
        score(t, "#status", 0);
        score(t, "#result", -999);
        score(t, "#trace", 1);

        result(t, source, ns, "recovery", 0, 0, 9);
        result(t, source, ns, "recovery", -4, -4, 9);
        PlayerAcceptance.server(t, "scoreboard players reset #input ledger.points");
        set(t, "#trace", 0);
        invoke(t, source, ns, "recovery");
        score(t, "#status", 1);
        score(t, "#result", -7);
        score(t, "#trace", 9);
        result(t, source, ns, "ignored", 0, 0, 7);
        result(t, source, ns, "batch", 0, 0, 234);
        result(t, source, ns, "empty-batch", 0, 0, 0);

        set(t, "#trace", 8);
        invoke(t, source, ns, "batch");
        score(t, "#status", 1);
        score(t, "#result", 0);
        score(t, "#trace", 8234);
        invoke(t, source, ns, "batch");
        score(t, "#status", 1);
        score(t, "#result", 0);
        score(t, "#trace", 8234234);
        invoke(t, source, ns, "empty-batch");
        score(t, "#status", 1);
        score(t, "#result", 0);
        score(t, "#trace", 8234234);
        PlayerAcceptance.server(t, "scoreboard players reset #trace ledger.points");
        invoke(t, source, ns, "empty-batch");
        score(t, "#status", 1);
        score(t, "#result", 0);
        absent(t, "#trace");
        invoke(t, source, ns, "batch");
        score(t, "#status", 0);
        score(t, "#result", -999);
        absent(t, "#trace");
    }

    private static void combinators(GameTestHelper t, CommandSourceStack source, String ns) {
        result(t, source, ns, "map", 0, 1, 0);
        result(t, source, ns, "map", -4, -7, 0);
        result(t, source, ns, "bind", 0, 10, 5);
        result(t, source, ns, "bind", 4, 14, 5);
        result(t, source, ns, "fallback", 0, 0, 0);
        result(t, source, ns, "fallback", -3, -3, 0);
        result(t, source, ns, "orelse", 0, 0, 0);
        result(t, source, ns, "is-success", 0, 1, 0);

        PlayerAcceptance.server(t, "scoreboard players reset #input ledger.points");
        for (String entry : new String[]{"map", "bind"}) {
            set(t, "#trace", 0);
            invoke(t, source, ns, entry);
            score(t, "#status", 0);
            score(t, "#result", -999);
            score(t, "#trace", 0);
        }
        set(t, "#trace", 0);
        invoke(t, source, ns, "fallback");
        score(t, "#status", 1);
        score(t, "#result", 44);
        score(t, "#trace", 8);
        set(t, "#trace", 0);
        invoke(t, source, ns, "is-success");
        score(t, "#status", 1);
        score(t, "#result", 0);
        score(t, "#trace", 0);

        set(t, "#fallback", 0);
        set(t, "#trace", 0);
        invoke(t, source, ns, "orelse");
        score(t, "#status", 1);
        score(t, "#result", 0);
        score(t, "#trace", 7);
        PlayerAcceptance.server(t, "scoreboard players reset #fallback ledger.points");
        set(t, "#trace", 0);
        invoke(t, source, ns, "orelse");
        score(t, "#status", 0);
        score(t, "#result", -999);
        score(t, "#trace", 7);
    }

    private static void run(GameTestHelper t) {
        var source = t.getLevel().getServer().createCommandSourceStack().withLevel(t.getLevel());
        for (String ns : new String[]{"ledger", "ledgerstack"}) {
            records(t, source, ns);
            ledger(t, source, ns);
            control(t, source, ns);
            combinators(t, source, ns);
        }
        t.succeed();
    }
}
