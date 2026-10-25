package oria.integration;

import java.util.List;
import java.util.Objects;
import net.minecraft.commands.CommandSourceStack;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.network.protocol.game.ClientboundClearTitlesPacket;
import net.minecraft.network.protocol.game.ClientboundSetActionBarTextPacket;
import net.minecraft.network.protocol.game.ClientboundSetSubtitleTextPacket;
import net.minecraft.network.protocol.game.ClientboundSetTitleTextPacket;
import net.minecraft.network.protocol.game.ClientboundSetTitlesAnimationPacket;
import net.minecraft.network.protocol.game.ClientboundSoundPacket;
import net.minecraft.network.protocol.game.ClientboundStopSoundPacket;
import net.minecraft.resources.Identifier;
import net.minecraft.sounds.SoundSource;
import net.minecraft.world.level.Level;
import net.minecraft.world.phys.Vec3;
import net.minecraft.world.scores.ScoreHolder;

/** Inspect native tag state and client packets produced by the compiled presentation library. */
final class PresentationAcceptance {
    private static void score(GameTestHelper test, String holder, int value) {
        PlayerAcceptance.score(test, ScoreHolder.forNameOnly(holder), "feedback.points", value);
    }

    private static void set(GameTestHelper test, String holder, int value) {
        PlayerAcceptance.server(test, "scoreboard players set " + holder + " feedback.points " + value);
    }

    private static void invoke(GameTestHelper test, CommandSourceStack source, String entry) {
        set(test, "#status", -1);
        PlayerAcceptance.command(test, source, "function feedback:" + entry);
        PlayerAcceptance.clean(test, "feedback");
    }

    private static void result(GameTestHelper test, int value) {
        score(test, "#status", 1);
        score(test, "#result", value);
    }

    private static void failed(GameTestHelper test) {
        score(test, "#status", 0);
        score(test, "#result", -999);
    }

    private static <T> T packet(GameTestHelper test, PlayerAcceptance.Player player, Class<T> type) {
        var packets = player.packets().stream().filter(type::isInstance).map(type::cast).toList();
        test.assertTrue(packets.size() == 1, "expected one " + type.getSimpleName() + ", got " + packets);
        return packets.getFirst();
    }

    private static void silent(GameTestHelper test, PlayerAcceptance.Player player) {
        test.assertTrue(player.packets().stream().noneMatch(p -> p instanceof ClientboundSoundPacket ||
            p instanceof ClientboundSetTitlesAnimationPacket || p instanceof ClientboundSetTitleTextPacket),
            "failed commands send no presentation packets");
    }

    static void run(GameTestHelper test, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var source = test.getLevel().getServer().createCommandSourceStack()
            .withLevel(test.getLevel()).withPosition(new Vec3(0, 64, 0));
        var self = source.withEntity(ada.entity());
        ada.packets();
        bob.packets();

        invoke(test, source, "tag-list");
        result(test, 0);
        invoke(test, self, "tag-self");
        result(test, 1);
        invoke(test, source, "tag-all");
        result(test, 1);
        test.assertTrue(ada.entity().entityTags().contains("round.active") &&
            bob.entity().entityTags().contains("round.active"), "tag adds reach both selected players");
        invoke(test, source, "tag-all");
        failed(test);
        set(test, "#continued", 0);
        invoke(test, source, "stopping");
        score(test, "#continued", 0);
        invoke(test, source, "continuing");
        score(test, "#continued", 2);
        invoke(test, source, "tag-list");
        result(test, 1);
        invoke(test, self, "tag-winner");
        result(test, 1);
        invoke(test, source, "tag-list");
        result(test, 2);
        invoke(test, source, "tag-remove");
        result(test, 2);
        invoke(test, source, "tag-remove");
        failed(test);
        invoke(test, source, "tag-list");
        result(test, 1);
        invoke(test, source, "tag-missing");
        failed(test);

        ada.packets();
        bob.packets();
        invoke(test, source, "title");
        result(test, 2);
        for (var player : List.of(ada, bob)) {
            test.assertTrue(packet(test, player, ClientboundSetTitleTextPacket.class).text().getString()
                .equals("Round one"), "literal title content");
        }
        invoke(test, source, "subtitle");
        result(test, 2);
        for (var player : List.of(ada, bob)) {
            test.assertTrue(packet(test, player, ClientboundSetSubtitleTextPacket.class).text().getString()
                .equals("Choose a move"), "subtitle content");
        }
        set(test, "#input", -12);
        invoke(test, source, "actionbar");
        result(test, 2);
        for (var player : List.of(ada, bob)) {
            test.assertTrue(packet(test, player, ClientboundSetActionBarTextPacket.class).text().getString()
                .equals("-12"), "dynamic action-bar number");
        }
        invoke(test, self, "rich");
        result(test, 1);
        var rich = packet(test, ada, ClientboundSetTitleTextPacket.class).text();
        test.assertTrue(rich.getString().equals("Ready") && rich.getStyle().isBold() &&
            rich.getStyle().getColor().getValue() == 0xffaa00, "NBT title styles");
        silent(test, bob);
        set(test, "#input", 35);
        invoke(test, source, "times");
        result(test, 2);
        for (var player : List.of(ada, bob)) {
            var timing = packet(test, player, ClientboundSetTitlesAnimationPacket.class);
            test.assertTrue(timing.getFadeIn() == 5 && timing.getStay() == 35 && timing.getFadeOut() == 24,
                "native seconds/ticks/days conversion");
        }
        set(test, "#input", -1);
        invoke(test, source, "times");
        failed(test);
        silent(test, ada);
        silent(test, bob);
        for (String entry : List.of("clear", "reset", "clear")) {
            invoke(test, source, entry);
            result(test, 2);
            for (var player : List.of(ada, bob)) {
                test.assertTrue(packet(test, player, ClientboundClearTitlesPacket.class).shouldResetTimes()
                    == entry.equals("reset"), "clear/reset packet distinction");
            }
        }
        invoke(test, source, "title-missing");
        failed(test);
        silent(test, ada);
        silent(test, bob);

        var adaPos = ada.entity().position();
        var bobPos = bob.entity().position();
        ada.entity().setPos(0, 64, 0);
        bob.entity().setPos(100, 64, 0);
        invoke(test, source, "sound");
        result(test, 1);
        var near = packet(test, ada, ClientboundSoundPacket.class);
        test.assertTrue(near.getSource() == SoundSource.UI && near.getVolume() == 1 && near.getPitch() == 1 &&
            near.getX() == 0 && near.getY() == 64 && near.getZ() == 0 &&
            near.getSound().value().location().equals(Identifier.parse("feedback:cue")), "sound packet parameters");
        silent(test, bob);
        invoke(test, source, "minimum");
        result(test, 2);
        near = packet(test, ada, ClientboundSoundPacket.class);
        var far = packet(test, bob, ClientboundSoundPacket.class);
        test.assertTrue(near.getVolume() == 1 && far.getVolume() == 0.25f && far.getX() == 98 &&
            far.getY() == 64 && far.getZ() == 0 && near.getSeed() == far.getSeed(), "minimum-volume relocation");
        set(test, "#input", 2);
        invoke(test, source, "pitch");
        result(test, 1);
        test.assertTrue(packet(test, ada, ClientboundSoundPacket.class).getPitch() == 2, "dynamic pitch");
        silent(test, bob);
        set(test, "#input", 3);
        invoke(test, source, "pitch");
        failed(test);
        silent(test, ada);
        silent(test, bob);
        set(test, "#input", 2);
        invoke(test, source, "positioned");
        result(test, 1);
        var moved = packet(test, ada, ClientboundSoundPacket.class);
        test.assertTrue(moved.getX() == 2 && moved.getY() == 64.25 && moved.getZ() == 0,
            "mixed dynamic and fractional sound coordinates");
        silent(test, bob);
        var nether = test.getLevel().getServer().getLevel(Level.NETHER);
        test.assertTrue(nether != null, "native fixture supplies the Nether");
        invoke(test, source.withLevel(nether), "minimum");
        failed(test);
        silent(test, ada);
        silent(test, bob);
        invoke(test, source, "sound-missing");
        failed(test);

        for (String entry : List.of("stop-all", "stop-channel", "stop-id", "stop-one", "stop-one")) {
            invoke(test, source.withLevel(nether), entry);
            result(test, 2);
            for (var player : List.of(ada, bob)) {
                var stop = packet(test, player, ClientboundStopSoundPacket.class);
                var channel = entry.equals("stop-channel") || entry.equals("stop-one") ? SoundSource.UI : null;
                var sound = entry.equals("stop-id") || entry.equals("stop-one") ? Identifier.parse("feedback:cue") : null;
                test.assertTrue(stop.getSource() == channel && Objects.equals(stop.getName(), sound),
                    "independent category and sound ID filters");
            }
        }
        ada.entity().setPos(adaPos);
        bob.entity().setPos(bobPos);
    }
}
