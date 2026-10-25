package oria.integration;

import java.util.List;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.network.protocol.common.ClientboundPostEffectsPacket;
import net.minecraft.network.protocol.game.ClientboundLevelParticlesPacket;
import net.minecraft.resources.Identifier;
import net.minecraft.world.InteractionHand;
import net.minecraft.world.item.SwingAnimationType;
import net.minecraft.world.scores.DisplaySlot;
import net.minecraft.world.scores.ScoreHolder;
import net.minecraft.world.scores.criteria.ObjectiveCriteria;
import net.minecraft.network.chat.numbers.BlankFormat;
import net.minecraft.network.chat.numbers.FixedFormat;
import net.minecraft.network.chat.numbers.StyledFormat;

import static oria.integration.BatchAcceptance.*;

final class DisplayControlAcceptance {
    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var s = source(t);
        var self = s.withEntity(ada.entity());
        ada.packets();
        bob.packets();
        result(t, s, "particles", 2);
        for (var p : List.of(ada, bob)) {
            var particles = p.packets().stream().filter(ClientboundLevelParticlesPacket.class::isInstance)
                .map(ClientboundLevelParticlesPacket.class::cast).toList();
            t.assertTrue(particles.size() == 1 && particles.getFirst().count() == 1 &&
                particles.getFirst().x() == 0 && particles.getFirst().y() == 64,
                "particle packet count and origin");
        }
        result(t, s, "particleDust", 2);
        result(t, s, "particleNbt", 2);
        result(t, s, "particleForce", 2);
        set(t, "#input", 4);
        result(t, s, "particleDynamic", 2);
        var packets = ada.packets().stream().filter(ClientboundLevelParticlesPacket.class::isInstance)
            .map(ClientboundLevelParticlesPacket.class::cast).toList();
        t.assertTrue(packets.getLast().count() == 4, "dynamic particle count");
        set(t, "#input", -1);
        fail(t, s, "particleDynamic");
        fail(t, s, "swingMarker");
        result(t, self, "swingHand", 1);
        t.assertTrue(ada.entity().getCurrentSwing().animation().type() == SwingAnimationType.WHACK,
            "default hand animation");
        result(t, self, "swingStab", 1);
        t.assertTrue(ada.entity().getCurrentSwing().hand() == InteractionHand.OFF_HAND &&
            ada.entity().getCurrentSwing().animation().type() == SwingAnimationType.STAB &&
            ada.entity().getCurrentSwing().durationTicks() == 10, "hand, animation, native duration");
        result(t, self, "swingNone", 1);
        set(t, "#input", 12);
        result(t, self, "swingDynamic", 1);
        t.assertTrue(ada.entity().getCurrentSwing().durationTicks() == 12, "dynamic swing duration");
        set(t, "#input", 0);
        fail(t, self, "swingDynamic");

        ada.entity().clearPostEffects();
        bob.entity().clearPostEffects();
        ada.packets();
        bob.packets();
        result(t, self, "postList", 0);
        result(t, s, "postAdd", 2);
        for (var p : List.of(ada, bob)) {
            t.assertTrue(p.entity().getPostEffects().equals(List.of(Identifier.parse("batch:gray"))),
                "post-effect state updated");
            t.assertTrue(p.packets().stream().noneMatch(ClientboundPostEffectsPacket.class::isInstance),
                "post-effect delivery is deferred to the player update");
            // Flush the native sender used by the player update, without advancing the whole world.
            p.entity().sendPostEffects();
            var effects = p.packets().stream().filter(ClientboundPostEffectsPacket.class::isInstance)
                .map(ClientboundPostEffectsPacket.class::cast).toList();
            t.assertTrue(effects.size() == 1 &&
                effects.getFirst().postEffects().equals(List.of(Identifier.parse("batch:gray"))),
                "post-effect resource packet");
        }
        fail(t, s, "postAdd");
        result(t, self, "postList", 1);
        result(t, s, "postRemove", 2);
        fail(t, s, "postRemove");
        result(t, s, "postAdd", 2);
        result(t, s, "postClear", 2);
        fail(t, s, "postClear");

        var board = t.getLevel().getScoreboard();
        var objective = board.getObjective("batch.points");
        result(t, s, "sidebar", 0);
        t.assertTrue(board.getDisplayObjective(DisplaySlot.SIDEBAR) == objective, "sidebar objective");
        fail(t, s, "sidebar");
        result(t, s, "belowName", 0);
        result(t, s, "listDisplay", 0);
        result(t, s, "teamSidebar", 0);
        result(t, s, "clearSidebar", 0);
        fail(t, s, "clearSidebar");
        result(t, s, "objectiveName", 0);
        t.assertTrue(objective.getDisplayName().getString().equals("Control"), "objective name");
        result(t, s, "objectiveHearts", 0);
        t.assertTrue(objective.getRenderType() == ObjectiveCriteria.RenderType.HEARTS, "heart rendering");
        result(t, s, "objectiveInteger", 0);
        result(t, s, "objectiveAuto", 0);
        t.assertFalse(objective.displayAutoUpdate(), "automatic names disabled");
        result(t, s, "objectiveBlank", 0);
        t.assertTrue(objective.numberFormat() instanceof BlankFormat, "blank objective format");
        result(t, s, "objectiveFixed", 0);
        t.assertTrue(objective.numberFormat().format(7).getString().equals("Round"), "fixed objective text");
        result(t, s, "objectiveStyle", 0);
        t.assertTrue(objective.numberFormat() instanceof StyledFormat &&
            objective.numberFormat().format(7).getStyle().isBold(), "NBT number style");
        result(t, s, "objectiveFormatReset", 0);
        t.assertTrue(objective.numberFormat() == null, "objective default format");

        result(t, s, "scoreName", 2);
        t.assertTrue(board.getOrCreatePlayerScore(ada.entity(), objective).display().getString().equals("Player"),
            "score display name");
        result(t, s, "scoreNameReset", 2);
        t.assertTrue(board.getOrCreatePlayerScore(ada.entity(), objective).display() == null, "score name reset");
        result(t, s, "scoreBlank", 2);
        result(t, s, "scoreFixed", 1);
        t.assertTrue(board.getPlayerScoreInfo(ScoreHolder.forNameOnly("#bot"), objective)
            .numberFormat() instanceof FixedFormat, "per-score fixed format");
        result(t, s, "scoreStyle", 2);
        t.assertTrue(board.getPlayerScoreInfo(ada.entity(), objective).numberFormat() instanceof StyledFormat,
            "per-score styled format");
        result(t, s, "scoreFormatReset", 2);
        t.assertTrue(board.getPlayerScoreInfo(ada.entity(), objective).numberFormat() == null, "score format reset");
        set(t, "#input", 23);
        result(t, s, "scoreDynamic", 1);
        t.assertTrue(board.getPlayerScoreInfo(ScoreHolder.forNameOnly("#bot"), objective)
            .numberFormat().format(0).getString().equals("23"), "dynamic text format");

        var team = board.addPlayerTeam("batch.control");
        board.addPlayerToTeam(ada.entity().getScoreboardName(), team);
        result(t, s, "teamFilter", 1);
        result(t, s, "teamExclude", 1);
        result(t, s, "teamEmptyFilter", 1);
        result(t, s, "teamAnyFilter", 1);
        board.removePlayerTeam(team);
        fail(t, s, "teamFilter");
        result(t, s, "teamEmptyFilter", 2);
        for (var slot : DisplaySlot.values())
            if (board.getDisplayObjective(slot) == objective) board.setDisplayObjective(slot, null);
    }
}
