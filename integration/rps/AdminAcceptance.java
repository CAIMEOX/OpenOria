package oria.integration;

import java.util.List;
import net.minecraft.commands.CommandSourceStack;
import net.minecraft.commands.Commands;
import net.minecraft.commands.functions.CommandFunction;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.gametest.framework.TestFunctionLoader;
import net.minecraft.network.protocol.common.ClientboundTransferPacket;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.server.permissions.LevelBasedPermissionSet;
import net.minecraft.server.players.NameAndId;
import net.minecraft.world.scores.ScoreHolder;

import static oria.integration.BatchAcceptance.score;
import static oria.integration.BatchAcceptance.set;

/** An isolated native server run for administrative commands and connection packets. */
public final class AdminAcceptance {
    public static void main(String[] args) throws Exception {
        TestFunctionLoader.registerLoader(registrar -> registrar.accept(
            ResourceKey.create(Registries.TEST_FUNCTION, Identifier.parse("rps_test:game")),
            AdminAcceptance::run));
        net.minecraft.gametest.Main.main(args);
    }

    private static void invoke(GameTestHelper t, CommandSourceStack s, String name) {
        set(t, "#status", -1);
        PlayerAcceptance.command(t, s, "function servercmd:" + name.toLowerCase());
        PlayerAcceptance.clean(t, "servercmd");
    }

    private static int ok(GameTestHelper t, CommandSourceStack s, String name) {
        invoke(t, s, name);
        t.assertTrue(score(t, "#status") == 1, name + " should succeed");
        return score(t, "#result");
    }

    private static void result(GameTestHelper t, CommandSourceStack s, String name, int expected) {
        int actual = ok(t, s, name);
        t.assertTrue(actual == expected, name + " expected " + expected + ", got " + actual);
    }

    private static void fail(GameTestHelper t, CommandSourceStack s, String name) {
        invoke(t, s, name);
        t.assertTrue(score(t, "#status") == 0, name + " should fail");
    }

    private static void permissions(GameTestHelper t) {
        var dispatcher = t.getLevel().getServer().getCommands().getDispatcher();
        var low = Commands.createCompilationContext(LevelBasedPermissionSet.GAMEMASTER);
        boolean rejected = false;
        try {
            CommandFunction.fromLines(Identifier.parse("servercmd:permission"), dispatcher, low,
                List.of("tick query"));
        } catch (IllegalArgumentException expected) {
            rejected = true;
        }
        t.assertTrue(rejected, "admin command rejected at function compilation permission 2");
        CommandFunction.fromLines(Identifier.parse("servercmd:permission"), dispatcher,
            Commands.createCompilationContext(LevelBasedPermissionSet.ADMIN), List.of("tick query"));
    }

    private static void ticks(GameTestHelper t, CommandSourceStack s) {
        var manager = t.getLevel().getServer().tickRateManager();
        float original = manager.tickrate();
        try {
            result(t, s, "tickRate", 30);
            t.assertTrue(manager.tickrate() == 30.5f, "fractional tick rate");
            result(t, s, "tickQuery", 30);
            set(t, "#input", 40);
            result(t, s, "tickDynamic", 40);
            set(t, "#input", 0);
            fail(t, s, "tickDynamic");
            fail(t, s, "tickStep");
            fail(t, s, "tickStopStep");
            fail(t, s, "tickStopSprint");
            result(t, s, "tickFreeze", 1);
            t.assertTrue(manager.isFrozen(), "freeze changes simulation state");
            result(t, s, "tickStep", 1);
            t.assertTrue(manager.isSteppingForward(), "step request active");
            result(t, s, "tickStopStep", 1);
            result(t, s, "tickUnfreeze", 0);
            result(t, s, "tickSprint", 1);
            t.assertTrue(manager.isSprinting(), "sprint request active");
            result(t, s, "tickStopSprint", 1);
        } finally {
            manager.stopStepping();
            manager.stopSprinting();
            manager.setFrozen(false);
            manager.setTickRate(original);
        }
    }

    private static void scores(GameTestHelper t, CommandSourceStack s, PlayerAcceptance.Player a,
            PlayerAcceptance.Player b) {
        var board = t.getLevel().getScoreboard();
        PlayerAcceptance.server(t, "scoreboard objectives add server.scores dummy");
        PlayerAcceptance.server(t, "scoreboard objectives add server.trigger trigger");
        result(t, s, "objectives", board.getObjectives().size());
        result(t, s, "scores", 0);
        result(t, s, "groupSet", 8);
        PlayerAcceptance.score(t, a.entity(), "server.scores", 4);
        PlayerAcceptance.score(t, b.entity(), "server.scores", 4);
        PlayerAcceptance.server(t, "scoreboard players set #server server.scores 2");
        result(t, s, "scores", 1);
        result(t, s, "groupAdd", 12);
        PlayerAcceptance.score(t, a.entity(), "server.scores", 6);
        result(t, s, "groupEnable", 2);
        fail(t, s, "groupEnable");
        set(t, "#input", -3);
        result(t, s, "groupDynamic", -6);
        set(t, "#input", Integer.MAX_VALUE);
        result(t, s, "groupDynamic", -2);
        PlayerAcceptance.server(t, "scoreboard players set #left server.scores 8");
        PlayerAcceptance.server(t, "scoreboard players set #right server.scores 5");
        result(t, s, "groupSwap", 5);
        PlayerAcceptance.score(t, ScoreHolder.forNameOnly("#right"), "server.scores", 8);
        fail(t, s, "groupDivideZero");
        PlayerAcceptance.score(t, ScoreHolder.forNameOnly("#zero"), "server.scores", 0);
        result(t, s, "holders", board.getTrackedPlayers().size());
        fail(t, s, "groupAbsent");
        result(t, s, "groupReset", 2);
        result(t, s, "groupReset", 2);
        result(t, s, "groupResetAll", 2);
        t.assertTrue(board.listPlayerScores(a.entity()).isEmpty(), "bulk reset removes all player scores");
        PlayerAcceptance.server(t, "scoreboard objectives remove server.scores");
        PlayerAcceptance.server(t, "scoreboard objectives remove server.trigger");
    }


    private static void transfers(GameTestHelper t, CommandSourceStack s, PlayerAcceptance.Player a,
            PlayerAcceptance.Player b) {
        a.packets(); b.packets();
        result(t, s.withEntity(a.entity()), "transfer", 1);
        t.assertTrue(a.packets().stream().anyMatch(p -> p instanceof ClientboundTransferPacket v &&
            v.host().equals("play.example.invalid") && v.port() == 25565), "default transfer port");
        t.assertTrue(b.packets().stream().noneMatch(ClientboundTransferPacket.class::isInstance),
            "self transfer has one recipient");
        result(t, s, "transferAll", 2);
        for (var p : List.of(a, b)) {
            t.assertTrue(p.packets().stream().anyMatch(packet -> packet instanceof ClientboundTransferPacket v &&
                v.port() == 25566), "group transfer destination");
        }
        set(t, "#input", 65535);
        result(t, s, "transferDynamic", 2);
        a.packets(); b.packets();
        for (int invalid : new int[]{0, 65536}) {
            set(t, "#input", invalid);
            fail(t, s, "transferDynamic");
        }
        // GameTestServer is unpublished, so Kick exercises its native publication guard.
        fail(t, s.withEntity(a.entity()), "kick");
        fail(t, s.withEntity(a.entity()), "kickReason");
    }

    private static void administration(GameTestHelper t, CommandSourceStack s) {
        var server = t.getLevel().getServer();
        var players = server.getPlayerList();
        var ghost = NameAndId.createOffline("AdminGhost");
        server.services().nameToIdCache().add(ghost);
        int timeout = server.playerIdleTimeout();
        boolean whitelist = server.isUsingWhitelist();
        try {
            result(t, s, "whitelistList", 0);
            result(t, s, "whitelistAdd", 1);
            fail(t, s, "whitelistAdd");
            result(t, s, "whitelistAddPlayers", 2);
            result(t, s, "whitelistList", 3);
            result(t, s, "whitelistOn", 1);
            fail(t, s, "whitelistOn");
            result(t, s, "whitelistReload", 1);
            result(t, s, "whitelistOff", 1);
            fail(t, s, "whitelistOff");
            result(t, s, "whitelistRemove", 1);
            fail(t, s, "whitelistRemove");
            result(t, s, "whitelistRemovePlayers", 2);
            result(t, s, "banList", 0);
            result(t, s, "ban", 1);
            fail(t, s, "ban");
            result(t, s, "banListPlayers", 1);
            result(t, s, "pardon", 1);
            fail(t, s, "pardon");
            result(t, s, "banReason", 1);
            t.assertTrue(players.getBans().get(ghost).getReason().equals("Testing policy"), "ban reason");
            result(t, s, "pardon", 1);
            result(t, s, "banIp", 0);
            fail(t, s, "banIp");
            result(t, s, "banListIps", 1);
            result(t, s, "pardonIp", 1);
            fail(t, s, "pardonIp");
            result(t, s, "banIpReason", 0);
            result(t, s, "pardonIp", 1);
            result(t, s, "op", 1);
            t.assertTrue(players.isOp(ghost), "operator grant persists");
            fail(t, s, "op");
            result(t, s, "deop", 1);
            fail(t, s, "deop");
            result(t, s, "idleTimeout", 5);
            t.assertTrue(server.playerIdleTimeout() == 5, "idle timeout changes server state");
            result(t, s, "idleOff", 0);
            set(t, "#input", 7);
            result(t, s, "idleDynamic", 7);
            set(t, "#input", -1);
            fail(t, s, "idleDynamic");
        } finally {
            server.setUsingWhitelist(whitelist);
            server.setPlayerIdleTimeout(timeout);
            players.getBans().remove(ghost);
            players.getIpBans().remove("192.0.2.1");
            players.getOps().remove(ghost);
            players.getWhiteList().remove(ghost);
            for (var p : players.getPlayers()) players.getWhiteList().remove(p.nameAndId());
        }
    }

    private static void run(GameTestHelper t) {
        var a = PlayerAcceptance.join(t, "AdminAda");
        var b = PlayerAcceptance.join(t, "AdminBob");
        var s = BatchAcceptance.source(t);
        permissions(t);
        ticks(t, s);
        scores(t, s, a, b);
        int enabled = ok(t, s, "packsEnabled");
        int available = ok(t, s, "packsAvailable");
        result(t, s, "packs", enabled + available);
        transfers(t, s, a, b);
        administration(t, s);
        t.succeed();
    }
}
