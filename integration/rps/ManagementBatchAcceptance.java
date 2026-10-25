package oria.integration;

import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.resources.Identifier;
import net.minecraft.world.BossEvent;
import net.minecraft.world.scores.Team;
import net.minecraft.world.scores.TeamColor;

import static oria.integration.BatchAcceptance.*;

final class ManagementBatchAcceptance {
    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var s = source(t);
        var bars = t.getLevel().getServer().getCustomBossEvents();
        int original = bars.getEvents().size();
        result(t, s, "barList", original);
        result(t, s, "barAdd", original + 1);
        fail(t, s, "barAdd");
        result(t, s, "barGetValue", 0);
        result(t, s, "barValue", 5);
        result(t, s, "barGetValue", 5);
        result(t, s, "barMax", 25);
        result(t, s, "barGetMax", 25);
        fail(t, s, "barMax");
        result(t, s, "barInvisible", 0);
        result(t, s, "barGetVisible", 0);
        fail(t, s, "barInvisible");
        result(t, s, "barVisible", 0);
        result(t, s, "barColor", 0);
        result(t, s, "barStyle", 0);
        result(t, s, "barName", 0);
        var bar = bars.get(Identifier.parse("batch:bar"));
        t.assertTrue(bar.getColor() == BossEvent.BossBarColor.RED &&
            bar.getOverlay() == BossEvent.BossBarOverlay.NOTCHED_10 &&
            bar.getName().getString().equals("Changed"), "boss-bar properties");
        result(t, s, "barPlayers", 2);
        result(t, s, "barGetPlayers", 2);
        fail(t, s, "barPlayers");
        result(t, s, "barNoPlayers", 0);
        result(t, s, "barGetPlayers", 0);
        set(t, "#input", 12);
        result(t, s, "barDynamic", 12);
        set(t, "#input", -1);
        fail(t, s, "barDynamic");
        result(t, s, "barRemove", original);
        fail(t, s, "barRemove");

        var board = t.getLevel().getScoreboard();
        int teams = board.getPlayerTeams().size();
        result(t, s, "teamList", teams);
        result(t, s, "teamAdd", teams + 1);
        fail(t, s, "teamAdd");
        result(t, s, "teamNamed", teams + 2);
        result(t, s, "teamMembers", 0);
        result(t, s, "teamJoin", 2);
        result(t, s, "teamFake", 1);
        result(t, s, "teamMembers", 3);
        result(t, s, "teamJoin", 2);
        result(t, s, "teamMembers", 3);
        for (String name : new String[]{"teamColor", "teamFire", "teamSight", "teamName",
                "teamNameTags", "teamDeathMessages", "teamCollision"}) {
            result(t, s, name, 0);
            fail(t, s, name);
        }
        result(t, s, "teamPrefix", 1);
        result(t, s, "teamSuffix", 1);
        var team = board.getPlayerTeam("batch.red");
        t.assertTrue(team.getColor().orElse(null) == TeamColor.RED && !team.isAllowFriendlyFire() &&
            !team.canSeeFriendlyInvisibles() && team.getNameTagVisibility() == Team.Visibility.HIDE_FOR_OTHER_TEAMS &&
            team.getDeathMessageVisibility() == Team.Visibility.NEVER &&
            team.getCollisionRule() == Team.CollisionRule.PUSH_OWN_TEAM &&
            team.getDisplayName().getString().equals("Red team"), "team properties");
        result(t, s, "teamResetColor", 0);
        t.assertTrue(team.getColor().isEmpty(), "team color reset");
        result(t, s, "teamLeave", 2);
        result(t, s, "teamMembers", 1);
        result(t, s.withEntity(ada.entity()), "teamSelf", 1);
        result(t, s, "teamEmpty", 2);
        fail(t, s, "teamEmpty");
        result(t, s, "teamLeaveFake", 0);
        result(t, s, "teamRemove", teams + 1);
        result(t, s, "teamRemoveBlue", teams);
    }
}
