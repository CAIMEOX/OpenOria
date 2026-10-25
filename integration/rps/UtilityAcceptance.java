package oria.integration;

import java.util.List;
import java.util.function.Predicate;
import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Holder;
import net.minecraft.core.HolderSet;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.network.chat.ChatType;
import net.minecraft.network.protocol.game.ClientboundDisguisedChatPacket;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.entity.ai.village.poi.PoiTypes;
import net.minecraft.world.level.biome.Biome;
import net.minecraft.world.level.biome.Biomes;
import net.minecraft.world.phys.Vec3;
import net.minecraft.world.scores.ScoreHolder;

import static oria.integration.BatchAcceptance.score;
import static oria.integration.BatchAcceptance.set;

final class UtilityAcceptance {
    private static void invoke(GameTestHelper t, CommandSourceStack s, String name) {
        set(t, "#status", -1);
        PlayerAcceptance.command(t, s, "function utility:" + name.toLowerCase());
        PlayerAcceptance.clean(t, "utility");
    }

    private static int ok(GameTestHelper t, CommandSourceStack s, String name) {
        invoke(t, s, name);
        t.assertTrue(score(t, "#status") == 1, name + " should succeed");
        return score(t, "#result");
    }

    private static void result(GameTestHelper t, CommandSourceStack s, String name, int n) {
        int actual = ok(t, s, name);
        t.assertTrue(actual == n, name + " expected " + n + ", got " + actual);
    }

    private static void fail(GameTestHelper t, CommandSourceStack s, String name) {
        invoke(t, s, name);
        t.assertTrue(score(t, "#status") == 0, name + " should fail");
    }

    private static List<ClientboundDisguisedChatPacket> chat(PlayerAcceptance.Player p) {
        return p.packets().stream().filter(ClientboundDisguisedChatPacket.class::isInstance)
            .map(ClientboundDisguisedChatPacket.class::cast).toList();
    }

    private static void received(GameTestHelper t, PlayerAcceptance.Player p, String text,
            ResourceKey<ChatType> type) {
        var packets = chat(p);
        t.assertTrue(packets.stream().anyMatch(packet -> packet.message().getString().equals(text) &&
            packet.chatType().chatType().is(type)), "chat packet " + text + " / " + type.identifier());
    }

    private static void messages(GameTestHelper t, CommandSourceStack s,
            PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var self = ada.entity().createCommandSourceStack().withPermission(s.permissions());
        ada.packets(); bob.packets();
        result(t, s, "say", 1);
        received(t, ada, "Round ready.", ChatType.SAY_COMMAND);
        received(t, bob, "Round ready.", ChatType.SAY_COMMAND);
        result(t, self, "emote", 1);
        received(t, bob, "waves", ChatType.EMOTE_COMMAND);
        ada.packets();
        result(t, self, "tellSelf", 1);
        var selfPackets = chat(ada);
        t.assertTrue(selfPackets.size() == 1 &&
            selfPackets.getFirst().chatType().chatType().is(ChatType.MSG_COMMAND_INCOMING),
            "function output suppression retains delivery and suppresses outgoing echo");
        t.assertTrue(chat(bob).isEmpty(), "private message stays with the receiver");
        result(t, s, "tellAll", 2);
        received(t, ada, "Everyone ready.", ChatType.MSG_COMMAND_INCOMING);
        received(t, bob, "Everyone ready.", ChatType.MSG_COMMAND_INCOMING);
        fail(t, s, "tellAbsent");
        result(t, self, "expanded", 1);
        received(t, bob, "Hello Ada score 7", ChatType.SAY_COMMAND);
        ada.packets();
        result(t, self, "native", 1);
        received(t, bob, "Native Ada", ChatType.SAY_COMMAND);
        ada.packets();
        result(t, s, "separated", 1);
        t.assertTrue(chat(bob).stream().anyMatch(p -> {
            String text = p.message().getString();
            return text.contains("Ada") && text.contains("Bob") && text.endsWith(" [distance=..1]");
        }), "joined suffix remains text rather than extending the selector");
        ada.packets();
        set(t, "#input", -27);
        result(t, s, "chatDynamic", 1);
        received(t, bob, "Round -27", ChatType.SAY_COMMAND);
        ada.packets();

        var board = t.getLevel().getScoreboard();
        board.removePlayerFromTeam(ada.entity().getScoreboardName());
        board.removePlayerFromTeam(bob.entity().getScoreboardName());
        fail(t, self, "team");
        var team = board.addPlayerTeam("utility.team");
        board.addPlayerToTeam(ada.entity().getScoreboardName(), team);
        board.addPlayerToTeam(bob.entity().getScoreboardName(), team);
        ada.packets(); bob.packets();
        result(t, self, "team", 2);
        received(t, bob, "Team ready.", ChatType.TEAM_MSG_COMMAND_INCOMING);
        ada.packets();
        board.removePlayerFromTeam(bob.entity().getScoreboardName());
        result(t, self, "team", 1);
        t.assertTrue(chat(bob).isEmpty(), "team membership filters recipients");
        var pig = t.spawn(EntityTypes.PIG, new BlockPos(2, 24, 2));
        board.addPlayerToTeam(pig.getScoreboardName(), team);
        result(t, s.withEntity(pig), "team", 1);
        board.removePlayerFromTeam(ada.entity().getScoreboardName());
        result(t, s.withEntity(pig), "team", 0);
        board.removePlayerTeam(team);
        pig.discard();
        ada.packets(); bob.packets();
    }

    private static void information(GameTestHelper t, CommandSourceStack s, PlayerAcceptance.Player ada) {
        var self = ada.entity().createCommandSourceStack().withPermission(s.permissions());
        ada.packets();
        int count = t.getLevel().getServer().getPlayerList().getPlayerCount();
        result(t, self, "players", count);
        t.assertTrue(ada.messages().stream().noneMatch(m -> m.contains("players online")),
            "function suppresses native list feedback");
        PlayerAcceptance.command(t, self, "list");
        t.assertTrue(ada.messages().stream().anyMatch(m -> m.contains("Ada") && m.contains("Bob")), "online names");
        result(t, self, "playersUuids", count);
        ada.messages();
        PlayerAcceptance.command(t, self, "list uuids");
        t.assertTrue(ada.messages().stream().anyMatch(m -> m.contains(ada.entity().getUUID().toString())), "UUID listing");
        result(t, self, "seed", (int)t.getLevel().getSeed());
        ada.messages();
        PlayerAcceptance.command(t, self, "seed");
        t.assertTrue(ada.messages().stream().anyMatch(m -> m.contains(Long.toString(t.getLevel().getSeed()))),
            "seed feedback retains the full long value");
        result(t, self, "version", 1);
        ada.messages();
        PlayerAcceptance.command(t, self, "version");
        t.assertTrue(ada.messages().stream().anyMatch(m -> m.contains("26.3")), "native version feedback");
    }

    private static void biome(GameTestHelper t, CommandSourceStack s, BlockPos p, String name,
            Predicate<Holder<Biome>> predicate) {
        var nearest = t.getLevel().findClosestBiome3d(predicate, p, 6400, 32, 64);
        if (nearest == null) fail(t, s, name);
        else result(t, s, name, (int)Math.floor(Math.sqrt((float)p.distSqr(nearest.getFirst()))));
    }

    private static void locate(GameTestHelper t, CommandSourceStack s, BlockPos p) {
        var level = t.getLevel();
        biome(t, s, p, "locateBiome", b -> b.is(Biomes.PLAINS));
        biome(t, s, p, "locateBiomes", b -> b.is(Biomes.PLAINS) || b.is(Biomes.THE_VOID));
        var poi = p.offset(3, 20, 4);
        level.getPoiManager().add(poi, level.registryAccess().lookupOrThrow(Registries.POINT_OF_INTEREST_TYPE)
            .getOrThrow(PoiTypes.MEETING));
        result(t, s, "locatePoi", 5);
        result(t, s, "locatePois", 5);
        level.getPoiManager().remove(poi);
        fail(t, s, "locateEmptyPoi");
        fail(t, s, "locateInvalidStructure");
        fail(t, s, "locateEmptyStructure");
        var village = level.registryAccess().lookupOrThrow(Registries.STRUCTURE).getOrThrow(
            ResourceKey.create(Registries.STRUCTURE, Identifier.parse("minecraft:village_plains")));
        var nearest = level.getChunkSource().getGenerator().findNearestMapStructure(
            level, HolderSet.direct(village), p, 100, false);
        if (nearest == null) fail(t, s, "locateVillage");
        else {
            var q = nearest.getFirst();
            int x = q.getX() - p.getX(), z = q.getZ() - p.getZ();
            result(t, s, "locateVillage", (int)Math.floor((float)Math.sqrt(x * x + z * z)));
        }
    }

    private static void scores(GameTestHelper t, CommandSourceStack s,
            PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        PlayerAcceptance.server(t, "scoreboard objectives add utility.scores dummy");
        result(t, s, "add", 2);
        result(t, s, "addZero", 2);
        result(t, s, "remove", -3);
        set(t, "#input", 3);
        result(t, s, "addDynamic", 0);
        result(t, s, "addZero", 0);
        set(t, "#input", 4);
        result(t, s, "removeDynamic", -4);
        set(t, "#input", -1);
        fail(t, s, "addDynamic");
        fail(t, s, "removeDynamic");
        PlayerAcceptance.server(t, "scoreboard players set Ada utility.scores 3");
        PlayerAcceptance.server(t, "scoreboard players set Bob utility.scores 5");
        result(t, s, "addPlayers", 12);
        result(t, s, "removePlayers", 10);
        PlayerAcceptance.server(t, "scoreboard players set #overflow utility.scores 2147483647");
        result(t, s, "overflowAdd", Integer.MIN_VALUE);
        result(t, s, "overflowRemove", Integer.MAX_VALUE);
        fail(t, s, "addAbsent");
        fail(t, s, "addMissingObjective");
        int total = ok(t, s, "addAll");
        var board = t.getLevel().getScoreboard();
        var objective = board.getObjective("utility.scores");
        int expected = 0;
        for (var holder : board.getTrackedPlayers()) {
            var value = board.getPlayerScoreInfo(holder, objective);
            if (value != null) expected += value.value();
        }
        t.assertTrue(total == expected, "wildcard update returns the I32 sum of resulting scores");
        PlayerAcceptance.server(t, "scoreboard objectives remove utility.scores");
    }

    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var p = t.absolutePos(new BlockPos(2, 40, 2));
        var s = BatchAcceptance.source(t).withPosition(Vec3.atLowerCornerOf(p));
        messages(t, s, ada, bob);
        information(t, s, ada);
        scores(t, s, ada, bob);
        locate(t, s, p);
    }
}
