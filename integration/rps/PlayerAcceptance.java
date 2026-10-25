package oria.integration;

import com.mojang.authlib.GameProfile;
import io.netty.channel.embedded.EmbeddedChannel;
import java.util.ArrayList;
import java.util.List;
import java.util.UUID;
import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.gametest.framework.TestFunctionLoader;
import net.minecraft.network.Connection;
import net.minecraft.network.protocol.PacketFlow;
import net.minecraft.network.protocol.game.ClientboundSystemChatPacket;
import net.minecraft.nbt.FloatTag;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.server.level.ServerPlayer;
import net.minecraft.server.network.CommonListenerCookie;
import net.minecraft.server.permissions.PermissionSet;
import net.minecraft.world.scores.ScoreHolder;

/** Native GameTest players exercise the generated datapack through its public entries. */
public final class PlayerAcceptance {
    public static void main(String[] args) throws Exception {
        TestFunctionLoader.registerLoader(registrar -> registrar.accept(
            ResourceKey.create(Registries.TEST_FUNCTION, Identifier.parse("rps_test:game")),
            PlayerAcceptance::run));
        net.minecraft.gametest.Main.main(args);
    }

    static void command(GameTestHelper test, CommandSourceStack source, String text) {
        var server = test.getLevel().getServer();
        server.getCommands().performPrefixedCommand(source, text);
    }

    static void server(GameTestHelper test, String text) {
        command(test, test.getLevel().getServer().createCommandSourceStack(), text);
    }

    private static void player(GameTestHelper test, ServerPlayer player, String text) {
        command(test, test.getLevel().getServer().createCommandSourceStack().withEntity(player), text);
    }

    // The native mock-player helper uses one fixed name. Scoreboard isolation needs distinct names.
    // Use its Connection / EmbeddedChannel / PlayerList setup with named game profiles.
    record Player(ServerPlayer entity, EmbeddedChannel channel) {
        List<Object> packets() {
            channel.runPendingTasks();
            var packets = new ArrayList<Object>();
            Object packet;
            while ((packet = channel.readOutbound()) != null) {
                packets.add(packet);
            }
            return packets;
        }

        List<String> messages() {
            return packets().stream().filter(ClientboundSystemChatPacket.class::isInstance)
                .map(ClientboundSystemChatPacket.class::cast).map(p -> p.content().getString()).toList();
        }
    }

    static Player join(GameTestHelper test, String name) {
        var server = test.getLevel().getServer();
        var profile = new GameProfile(UUID.randomUUID(), name);
        var cookie = CommonListenerCookie.createInitial(profile, false);
        var player = new ServerPlayer(server, test.getLevel(), profile, cookie.clientInformation());
        var connection = new Connection(PacketFlow.SERVERBOUND);
        var channel = new EmbeddedChannel(connection);
        server.getPlayerList().placeNewPlayer(connection, player, cookie);
        return new Player(player, channel);
    }

    static void score(GameTestHelper test, ScoreHolder player, String objective, int n) {
        var board = test.getLevel().getScoreboard();
        var value = board.getPlayerScoreInfo(player, board.getObjective(objective));
        test.assertTrue(value != null && value.value() == n,
            objective + " expected " + n + ", got " + (value == null ? "absent" : value.value()));
    }

    private static void state(GameTestHelper test, Player player, int active, int p, int c) {
        score(test, player.entity(), "rps.active", active);
        score(test, player.entity(), "rps.player", p);
        score(test, player.entity(), "rps.server", c);
        score(test, player.entity(), "rps.input", 0);
        var board = test.getLevel().getScoreboard();
        test.assertFalse(board.getPlayerScoreInfo(player.entity(), board.getObjective("rps.input")).isLocked(),
            "input must be enabled after processing");
    }

    private static void trigger(GameTestHelper test, Player player, int n, boolean succeeds) {
        var result = new int[]{0, 0};
        var source = player.entity().createCommandSourceStack()
            .withPermission(PermissionSet.NO_PERMISSIONS)
            .withCallback((ok, value) -> { result[0] = ok ? 1 : 0; result[1] = value; });
        command(test, source, "trigger rps.input set " + n);
        test.assertTrue((result[0] == 1) == succeeds, "trigger success for " + n);
        if (succeeds) {
            test.assertTrue(result[1] == n, "trigger result for " + n);
            var board = test.getLevel().getScoreboard();
            test.assertTrue(board.getPlayerScoreInfo(player.entity(), board.getObjective("rps.input")).isLocked(),
                "trigger locks before the next tick");
        }
    }

    private static void tick(GameTestHelper test) {
        server(test, "function rpstest:fixed-tick");
        clean(test, "rpstest");
    }

    static void clean(GameTestHelper test, String namespace) {
        var storage = test.getLevel().getServer().getCommandStorage()
            .get(Identifier.parse(namespace + ":runtime"));
        for (String key : new String[]{"stack", "arena", "draft", "heap_arg", "nbt_args", "nbt_input"}) {
            test.assertFalse(storage.contains(key), namespace + " left invocation storage: " + key);
        }
    }

    private static void input(GameTestHelper test, Player player, int n) {
        trigger(test, player, n, true);
        tick(test);
    }

    private static void message(GameTestHelper test, Player player, String text) {
        var messages = player.messages();
        test.assertTrue(messages.stream().anyMatch(s -> s.contains(text)),
            "expected chat containing '" + text + "', got " + messages);
    }

    private static void judges(GameTestHelper test, Player player) {
        server(test, "scoreboard objectives add rps.result dummy");
        int[][] expected = {{0, -1, 1}, {1, 0, -1}, {-1, 1, 0}};
        for (int p = 1; p <= 3; p++) {
            for (int c = 1; c <= 3; c++) {
                player(test, player.entity(), "scoreboard players set @s rps.player " + p);
                player(test, player.entity(), "scoreboard players set @s rps.server " + c);
                player(test, player.entity(), "function rpstest:judge");
                score(test, player.entity(), "rps.result", expected[p - 1][c - 1]);
            }
        }
    }

    private static void submissions(GameTestHelper test, Player player) {
        for (String entry : new String[]{"trigger-set", "trigger-add", "trigger"}) {
            int expected = switch (entry) { case "trigger-set" -> 0; case "trigger-add" -> -3; default -> -2; };
            player(test, player.entity(), "scoreboard players enable @s sbtest.choice");
            server(test, "scoreboard players set #n sbtest.oria " + (entry.equals("trigger-set") ? 0 : -3));
            player(test, player.entity(), "function sbtest:" + entry);
            score(test, ScoreHolder.forNameOnly("#status"), "sbtest.oria", 1);
            score(test, ScoreHolder.forNameOnly("#result"), "sbtest.oria", expected);
            score(test, player.entity(), "sbtest.choice", expected);
            player(test, player.entity(), "function sbtest:" + entry);
            score(test, ScoreHolder.forNameOnly("#status"), "sbtest.oria", 0);
            score(test, player.entity(), "sbtest.choice", expected);
        }
        clean(test, "sbtest");
    }

    private static void literals(GameTestHelper test, Player player) {
        int[][] cases = {
            {Integer.MIN_VALUE, 7, 11}, {-1, 0, 12}, {-1, 7, 7}, {0, -23, -23},
            {Integer.MAX_VALUE, 7, 13}, {37, -8, -8}
        };
        for (int[] sample : cases) {
            player(test, player.entity(), "scoreboard players set @s rps.player " + sample[0]);
            player(test, player.entity(), "scoreboard players set @s rps.server " + sample[1]);
            player(test, player.entity(), "function rpstest:literals");
            score(test, player.entity(), "rps.result", sample[2]);
            clean(test, "rpstest");
        }
    }

    private static void arguments(GameTestHelper test, Player ada, Player bob) {
        score(test, ScoreHolder.forNameOnly("#arithmetic"), "argtest.points", 20);
        score(test, ScoreHolder.forNameOnly("#mod"), "argtest.points", -1);
        score(test, ScoreHolder.forNameOnly("#power_failed"), "argtest.points", 1);
        score(test, ScoreHolder.forNameOnly("#dynamic"), "argtest.points", -7);
        var data = test.getLevel().getServer().getCommandStorage().get(Identifier.parse("argtest:data"));
        test.assertTrue(data.get("power") instanceof FloatTag n && n.floatValue() == 0.0f,
            "data compute uses zero for a provider evaluation error");

        ada.entity().addTag("argtest");
        bob.entity().addTag("argtest");
        player(test, ada.entity(), "scoreboard players set @s argtest.points 2");
        player(test, bob.entity(), "scoreboard players set @s argtest.points 4");
        server(test, "function argtest:filter");
        score(test, ada.entity(), "argtest.points", 9);
        score(test, bob.entity(), "argtest.points", 4);

        player(test, ada.entity(), "function argtest:decimal");
        test.assertTrue(ada.entity().getX() == 1.0 && ada.entity().getY() == 65.25 &&
            ada.entity().getZ() == 1.0, "decimal coordinates retain exact positions");
        player(test, ada.entity(), "function argtest:integer");
        test.assertTrue(ada.entity().getX() == 1.5 && ada.entity().getY() == 65.25 &&
            ada.entity().getZ() == 1.5, "absolute integer x/z coordinates use native centering");
        player(test, ada.entity(), "execute at @s run function argtest:mixed");
        test.assertTrue(ada.entity().getX() == 3.5 && ada.entity().getY() == 66.25 &&
            ada.entity().getZ() == 1.0,
            "mixed coordinates expected (3.5, 66.25, 1.0), got " + ada.entity().position());
        clean(test, "argtest");
    }

    private static void run(GameTestHelper test) {
        WorldBatchAcceptance.run(test);
        EntityAcceptance.run(test);
        var ada = join(test, "Ada");
        var bob = join(test, "Bob");
        PlayerBatchAcceptance.run(test, ada, bob);
        ManagementBatchAcceptance.run(test, ada, bob);
        ControlAcceptance.run(test, ada, bob);
        ItemContentAcceptance.run(test, ada, bob);
        ExecutionAcceptance.run(test, ada, bob);
        GenerationAcceptance.run(test, ada, bob);
        UtilityAcceptance.run(test, ada, bob);
        PresentationAcceptance.run(test, ada, bob);
        arguments(test, ada, bob);
        submissions(test, ada);
        judges(test, ada);
        literals(test, ada);
        // A first tick initializes independent state and enables permission-free player input.
        tick(test);
        state(test, ada, 0, 0, 0);
        state(test, bob, 0, 0, 0);
        input(test, ada, 1);
        state(test, ada, 0, 0, 0);
        message(test, ada, "Start a match");

        input(test, ada, 4);
        state(test, ada, 1, 0, 0);
        message(test, ada, "First to two wins");
        input(test, bob, 4);
        // One accepted trigger locks input. A second command cannot overwrite it before polling.
        trigger(test, ada, 1, true);
        trigger(test, ada, 2, false);
        score(test, ada.entity(), "rps.input", 1);
        trigger(test, bob, 2, true);
        tick(test);
        state(test, ada, 1, 1, 0);
        state(test, bob, 1, 0, 1);
        message(test, ada, "You win the round");
        message(test, bob, "The server wins the round");
        tick(test);
        state(test, ada, 1, 1, 0);
        state(test, bob, 1, 0, 1);

        // Draws and invalid values preserve scores and leave the next input enabled.
        input(test, ada, 3);
        state(test, ada, 1, 1, 0);
        message(test, ada, "Draw. Choose again.");
        for (int invalid : new int[]{-1, 5, Integer.MIN_VALUE, Integer.MAX_VALUE}) {
            input(test, ada, invalid);
            state(test, ada, 1, 1, 0);
            message(test, ada, "Choose 1 = rock");
        }
        input(test, ada, 0);
        state(test, ada, 1, 1, 0);

        // Two rounds can finish 2-0 in either direction; finished matches retain the final score.
        input(test, ada, 1);
        state(test, ada, 0, 2, 0);
        message(test, ada, "You win the match!");
        input(test, ada, 1);
        state(test, ada, 0, 2, 0);
        input(test, bob, 2);
        state(test, bob, 0, 0, 2);
        message(test, bob, "The server wins the match.");

        // Restarting and reaching 1-1 exercise the third deciding round.
        input(test, ada, 4);
        input(test, ada, 1);
        input(test, ada, 2);
        state(test, ada, 1, 1, 1);
        input(test, ada, 1);
        state(test, ada, 0, 2, 1);
        input(test, ada, 4);
        input(test, ada, 1);
        input(test, ada, 2);
        input(test, ada, 2);
        state(test, ada, 0, 1, 2);

        // A draw action can fail: the input is consumed, and no round is scored or replayed.
        input(test, ada, 4);
        trigger(test, ada, 1, true);
        server(test, "function rpstest:failed-tick");
        clean(test, "rpstest");
        state(test, ada, 1, 0, 0);
        tick(test);
        state(test, ada, 1, 0, 0);
        input(test, ada, 1);
        input(test, bob, 4);
        input(test, bob, 2);
        state(test, ada, 1, 1, 0);
        state(test, bob, 1, 0, 1);

        // Restart an active match and verify that the other player's progress is retained.
        input(test, ada, 4);
        state(test, ada, 1, 0, 0);
        state(test, bob, 1, 0, 1);
        input(test, ada, 1);

        // Exercise Minecraft's asynchronous resource reload and the actual load/tick callbacks.
        var server = test.getLevel().getServer();
        var reloaded = server.reloadResources(server.getPackRepository().getSelectedIds());
        test.startSequence()
            .thenWaitUntil(() -> test.assertTrue(reloaded.isDone(), "resource reload is pending"))
            .thenIdle(2)
            .thenExecute(() -> {
                test.assertFalse(reloaded.isCompletedExceptionally(), "resource reload failed");
                state(test, ada, 1, 1, 0);
                state(test, bob, 1, 0, 1);
                // The production random tick consumes an accepted input on its own.
                ada.messages();
                trigger(test, ada, 1, true);
            })
            .thenIdle(2)
            .thenExecute(() -> {
                score(test, ada.entity(), "rps.input", 0);
                var messages = ada.messages();
                test.assertTrue(messages.stream().filter(s -> s.startsWith("Server chose ")).count() == 1,
                    "one production random draw and announcement per accepted input: " + messages);
                var board = test.getLevel().getScoreboard();
                int p = board.getPlayerScoreInfo(ada.entity(), board.getObjective("rps.player")).value();
                int c = board.getPlayerScoreInfo(ada.entity(), board.getObjective("rps.server")).value();
                test.assertTrue((p == 1 && c == 0) || (p == 2 && c == 0) || (p == 1 && c == 1),
                    "one valid production round: " + p + "-" + c);
                state(test, bob, 1, 0, 1);
                clean(test, "rps");
            })
            .thenSucceed();
    }
}
