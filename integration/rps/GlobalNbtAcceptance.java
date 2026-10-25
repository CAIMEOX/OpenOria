package oria.integration;

import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.gametest.framework.TestFunctionLoader;
import net.minecraft.core.registries.Registries;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.scores.ScoreHolder;
import net.minecraft.nbt.CompoundTag;
import net.minecraft.nbt.IntTag;

/** Observe named native documents across entries, reload checks, and task slices. */
public final class GlobalNbtAcceptance {
    public static void main(String[] args) throws Exception {
        TestFunctionLoader.registerLoader(registrar -> registrar.accept(
            ResourceKey.create(Registries.TEST_FUNCTION, Identifier.parse("rps_test:game")), GlobalNbtAcceptance::run));
        net.minecraft.gametest.Main.main(args);
    }

    private static int score(GameTestHelper t, String ns, String holder) {
        var board = t.getLevel().getScoreboard();
        var result = board.getPlayerScoreInfo(ScoreHolder.forNameOnly(holder), board.getObjective(ns + ".oria"));
        return result == null ? 0 : result.value();
    }

    private static CompoundTag data(GameTestHelper t, String ns) {
        return t.getLevel().getServer().getCommandStorage().get(Identifier.parse(ns + ":state"));
    }

    private static int count(GameTestHelper t, String ns) {
        return data(t, ns).getCompoundOrEmpty("buffer").getIntOr("count", -1);
    }

    private static void call(GameTestHelper t, String ns, String path) {
        PlayerAcceptance.server(t, "function " + ns + ":" + path);
    }

    private static void ready(GameTestHelper t, String ns, int expected) {
        t.assertTrue(score(t, ns, "#ready") == expected, ns + " global readiness differs");
        t.assertTrue(score(t, ns, "#panic") == 1 - expected, ns + " initialization panic differs");
        t.assertTrue(score(t, ns, "#phase") == 0, ns + " initialization retained the execution phase");
    }

    private static void run(GameTestHelper t) {
        var storage = t.getLevel().getServer().getCommandStorage();
        String[] variants = {"global_test", "global_stack"};
        for (String ns : variants) {
            ready(t, ns, 1);
            t.assertTrue(count(t, ns) == 0, ns + " initializer did not run");
            var outside = data(t, ns);
            outside.putInt("external", 55);
            storage.set(Identifier.parse(ns + ":state"), outside);
            call(t, ns, "increment");
            call(t, ns, "increment");
            t.assertTrue(count(t, ns) == 2, ns + " value did not survive entry cleanup");
            call(t, ns, "__oria/load");
            ready(t, ns, 1);
            t.assertTrue(count(t, ns) == 2, ns + " reload reset global contents");
            t.assertTrue(data(t, ns).getIntOr("external", -1) == 55, ns + " reload changed unowned data");
            call(t, ns, "exercise");
            t.assertTrue(score(t, ns, "#entry_success") == 1, ns + " typed global operations failed");
            var doc = data(t, ns).getCompoundOrEmpty("buffer");
            t.assertTrue(doc.getIntOr("count", -1) == 9 &&
                doc.getListOrEmpty("values").get(0).equals(IntTag.valueOf(8)) &&
                doc.getStringOr("label", "").equals("replaced"), ns + " copy/replacement result differs");
            t.assertTrue(data(t, ns).getCompoundOrEmpty("neighbor").getIntOr("count", -1) == 100,
                ns + " disjoint global changed");
            call(t, ns, "foreign");
            t.assertTrue(score(t, ns, "#entry_success") == 1 && count(t, ns) == 77,
                ns + " command write did not invalidate cached data");
            call(t, ns, "repair");
            t.assertTrue(score(t, ns, "#entry_success") == 1 &&
                data(t, ns).getCompoundOrEmpty("buffer").getStringOr("label", "").equals("recreated") &&
                data(t, ns).getCompoundOrEmpty("buffer").getListOrEmpty("values").getIntOr(0, -1) == 30,
                ns + " typed native set, clear, and copy must create missing compound fields");

            var id = Identifier.parse(ns + ":persistent");
            var metadata = storage.get(id);
            var schema = metadata.get("globals");
            t.assertTrue(!metadata.contains("slots"), ns + " globals allocated a managed heap");
            metadata.putString("globals", "incompatible schema");
            storage.set(id, metadata);
            call(t, ns, "__oria/load");
            ready(t, ns, 0);
            call(t, ns, "increment");
            t.assertTrue(count(t, ns) == 77, ns + " schema mismatch modified user data");
            metadata = storage.get(id);
            metadata.put("globals", schema);
            storage.set(id, metadata);
            call(t, ns, "__oria/load");
            ready(t, ns, 1);

            var saved = data(t, ns).copy();
            var missing = data(t, ns);
            missing.remove("buffer");
            storage.set(Identifier.parse(ns + ":state"), missing);
            call(t, ns, "__oria/load");
            ready(t, ns, 0);
            t.assertTrue(!data(t, ns).contains("buffer"), ns + " missing initialized root was silently reset");
            storage.set(Identifier.parse(ns + ":state"), saved);
            call(t, ns, "__oria/load");
            ready(t, ns, 1);
        }

        String managed = "global_managed";
        ready(t, "global_renamed", 1);
        call(t, "global_renamed", "increment");
        t.assertTrue(count(t, "global_renamed") == 1 && count(t, "global_test") == 77,
            "changing Spec.ns did not isolate the same global declaration");
        ready(t, managed, 1);
        call(t, managed, "save");
        t.assertTrue(score(t, managed, "#entry_success") == 1, "global snapshot promotion failed");
        call(t, managed, "gc");
        call(t, managed, "__oria/load");
        ready(t, managed, 1);
        call(t, managed, "inspect");
        t.assertTrue(score(t, managed, "#entry_success") == 1 && count(t, managed) == 24,
            "managed snapshot and native global did not survive collection/reload independently");

        int[] variant = {0};
        boolean[] started = {false};
        boolean[] changed = {false};
        int[] before = {0};
        t.onEachTick(() -> {
            String ns = variants[variant[0]];
            if (!started[0]) {
                before[0] = count(t, ns);
                call(t, ns, "work");
                started[0] = true;
                return;
            }
            if (!changed[0] && score(t, ns, "#task.slices") == 1 && score(t, ns, "#task.phase") == 1) {
                call(t, ns, "interfere");
                changed[0] = true;
            }
            if (score(t, ns, "#task.phase") != 0) return;
            t.assertTrue(changed[0] && score(t, ns, "#task.status") == 2 && count(t, ns) == before[0] + 11,
                ns + " task reused a global read across suspension");
            if (++variant[0] == variants.length) t.succeed();
            else {
                started[0] = false;
                changed[0] = false;
            }
        });
    }
}
