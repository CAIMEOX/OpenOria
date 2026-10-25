package oria.integration;

import java.util.Arrays;
import java.util.Random;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.gametest.framework.TestFunctionLoader;
import net.minecraft.nbt.IntTag;
import net.minecraft.nbt.ListTag;
import net.minecraft.nbt.StringTag;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.level.gamerules.GameRules;
import net.minecraft.world.scores.ScoreHolder;

/** Sort runtime NBT inputs using the generated program and native storage. */
public final class MergeSortAcceptance {
    private static final Identifier STORE = Identifier.parse("merge_sort:state");

    public static void main(String[] args) throws Exception {
        TestFunctionLoader.registerLoader(registrar -> registrar.accept(
            ResourceKey.create(Registries.TEST_FUNCTION, Identifier.parse("rps_test:game")), MergeSortAcceptance::run));
        net.minecraft.gametest.Main.main(args);
    }

    private static int score(GameTestHelper t, String ns, String holder) {
        var board = t.getLevel().getScoreboard();
        var value = board.getPlayerScoreInfo(ScoreHolder.forNameOnly(holder), board.getObjective(ns + ".oria"));
        return value == null ? 0 : value.value();
    }

    private static void seed(GameTestHelper t, int[] input) {
        var store = t.getLevel().getServer().getCommandStorage();
        var data = store.get(STORE);
        var list = new ListTag();
        for (int n : input) list.add(IntTag.valueOf(n));
        data.put("input", list);
        store.set(STORE, data);
    }

    private static void seedInvalid(GameTestHelper t) {
        var store = t.getLevel().getServer().getCommandStorage();
        var data = store.get(STORE);
        var list = new ListTag();
        list.add(StringTag.valueOf("not a number"));
        list.add(IntTag.valueOf(0));
        data.put("input", list);
        store.set(STORE, data);
    }

    private static void check(GameTestHelper t, String key, int[] expected) {
        var data = t.getLevel().getServer().getCommandStorage().get(STORE);
        t.assertTrue(data.contains(key), "missing sorting " + key);
        var values = data.getListOrEmpty(key);
        t.assertTrue(values.size() == expected.length, "sorting changed " + key + " length");
        for (int i = 0; i < expected.length; i++) {
            t.assertTrue(values.get(i).equals(IntTag.valueOf(expected[i])),
                key + "[" + i + "] differs from expected " + expected[i]);
        }
    }

    private static void run(GameTestHelper t) {
        for (String ns : new String[]{"typed_nbt", "typed_nbt_stack"}) {
            for (String name : new String[]{"forward", "alias", "indices", "resize", "call", "failure", "join"}) {
                PlayerAcceptance.server(t, "function " + ns + ":memory/" + name);
                t.assertTrue(score(t, ns, "#entry_success") == 1,
                    ns + " memory optimization case failed: " + name);
            }
        }
        PlayerAcceptance.server(t, "function typed_nbt:run");
        var typed = t.getLevel().getServer().getCommandStorage().get(Identifier.parse("typed_nbt:result"));
        var typedValues = typed.getListOrEmpty("values");
        t.assertTrue(typedValues.size() == 1 && typedValues.get(0).equals(IntTag.valueOf(8)),
            "typed NBT update/copy/clear result is incorrect: " + typed +
            ", entry=" + score(t, "typed_nbt", "#entry_success") +
            ", ok=" + score(t, "typed_nbt", "#nbt_ok"));
        t.assertTrue(typed.contains("empty") && typed.getListOrEmpty("empty").isEmpty(),
            "typed NBT out-of-bounds assignment did not fail");
        var nested = typed.getCompoundOrEmpty("nested");
        t.assertTrue(nested.getCompoundOrEmpty("item").getIntOr("score", -1) == 41 &&
            nested.getListOrEmpty("colors").get(0).equals(StringTag.valueOf("red")),
            "derived nested record/enum encoding is incorrect");
        t.assertTrue(typed.getIntOr("persistentRead", -1) == 23,
            "persistent snapshot scalar query is incorrect");
        PlayerAcceptance.server(t, "function typed_nbt:gc");
        PlayerAcceptance.server(t, "function typed_nbt:restore");
        var snapshot = t.getLevel().getServer().getCommandStorage()
            .get(Identifier.parse("typed_nbt:result")).getListOrEmpty("snapshot");
        t.assertTrue(snapshot.size() == 1 && snapshot.get(0).equals(IntTag.valueOf(8)),
            "snapshot changed after source mutation, arena reset, or collection");
        t.getLevel().getGameRules().set(GameRules.MAX_COMMAND_SEQUENCE_LENGTH, 2048, t.getLevel().getServer());
        int[] reverse = new int[65];
        for (int i = 0; i < reverse.length; i++) reverse[i] = reverse.length - i;
        int[] random = new Random(907).ints(129, -100, 101).toArray();
        int[][] inputs = {
            {3, -2, 3, 0, 1}, {}, {Integer.MIN_VALUE},
            {Integer.MAX_VALUE, 0, Integer.MIN_VALUE, -1, Integer.MAX_VALUE, Integer.MIN_VALUE, 1},
            {-5, -1, 0, 0, 1, Integer.MAX_VALUE},
            {-5, -1, 0, 0, 1, Integer.MAX_VALUE},
            {7, 7, 7, 7, 7, 7, 7}, reverse, random
        };
        String[] variants = {"merge_sort", "merge_sort_stack"};
        int[] variant = {0};
        int[] example = {0};
        boolean[] started = {false};
        boolean[] cancelled = {false};
        int[] recovered = {0, Integer.MIN_VALUE, 3, -2};
        int[] previous = random.clone();
        Arrays.sort(previous);
        t.onEachTick(() -> {
            String ns = variants[variant[0]];
            int job = example[0];
            int[] input = job < inputs.length ? inputs[job] :
                job == inputs.length + 2 ? recovered : random;
            if (!started[0]) {
                if (job == inputs.length) seedInvalid(t);
                else seed(t, input);
                PlayerAcceptance.server(t, "function " + ns + ":sort");
                started[0] = true;
                cancelled[0] = false;
            }
            if (score(t, ns, "#task.phase") != 0) {
                var workspace = t.getLevel().getServer().getCommandStorage().get(Identifier.parse(ns + ".task:runtime"));
                t.assertTrue(workspace.getListOrEmpty("arena").size() <= 2,
                    "sorting allocated per-element snapshots");
                if (job == inputs.length + 1 && score(t, ns, "#task.slices") >= 2) {
                    PlayerAcceptance.server(t, "function " + ns + ":sort/cancel");
                    cancelled[0] = true;
                } else return;
            }
            if (job == inputs.length) {
                t.assertTrue(score(t, ns, "#task.status") == 3, "non-numeric head did not fail sorting");
                check(t, "output", previous);
            } else if (job == inputs.length + 1) {
                t.assertTrue(cancelled[0] && score(t, ns, "#task.status") == 5, "sorting cancellation failed");
                check(t, "input", input);
                check(t, "output", previous);
            } else {
                int[] expected = input.clone();
                Arrays.sort(expected);
                t.assertTrue(score(t, ns, "#task.status") == 2,
                    ns + " sorting case " + job + " failed with status " + score(t, ns, "#task.status"));
                check(t, "input", input);
                check(t, "output", expected);
                if (input.length >= 65) {
                    t.assertTrue(score(t, ns, "#task.slices") > 1, "sorting did not cross ticks");
                    t.assertTrue(score(t, ns, "#task.parks") > 0, "sorting did not park for fuel");
                }
            }
            var workspace = t.getLevel().getServer().getCommandStorage().get(Identifier.parse(ns + ".task:runtime"));
            for (String key : new String[]{"arena", "draft", "nbt_args", "nbt_input"})
                t.assertTrue(!workspace.contains(key), "sorting workspace survived completion: " + key);
            t.assertTrue(workspace.getCompoundOrEmpty("macro").isEmpty(),
                "sorting macro scratch survived completion");
            started[0] = false;
            if (++example[0] == inputs.length + 3) {
                example[0] = 0;
                if (++variant[0] == variants.length) t.succeed();
            }
        });
    }
}
