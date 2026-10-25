package oria.integration;

import java.util.List;
import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Holder;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.world.effect.MobEffect;
import net.minecraft.world.effect.MobEffects;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.entity.LivingEntity;
import net.minecraft.world.phys.Vec3;
import net.minecraft.world.scores.ScoreHolder;

/** Native state assertions for the compiled Kill, Summon, and Effect interfaces. */
final class EntityAcceptance {
    private static void score(GameTestHelper test, String holder, int value) {
        PlayerAcceptance.score(test, ScoreHolder.forNameOnly(holder), "entitytest.points", value);
    }

    private static void set(GameTestHelper test, String holder, int value) {
        PlayerAcceptance.server(test, "scoreboard players set " + holder + " entitytest.points " + value);
    }

    private static void invoke(GameTestHelper test, CommandSourceStack source, String entry) {
        set(test, "#status", -1);
        PlayerAcceptance.command(test, source, "function entitytest:" + entry);
        PlayerAcceptance.clean(test, "entitytest");
    }

    private static void result(GameTestHelper test, int value) {
        score(test, "#status", 1);
        score(test, "#result", value);
    }

    private static void failed(GameTestHelper test) {
        score(test, "#status", 0);
        score(test, "#result", -999);
    }

    private static void effect(GameTestHelper test, List<? extends LivingEntity> entities,
            Holder<MobEffect> type, int duration, int amplifier, boolean visible) {
        for (var entity : entities) {
            var instance = entity.getEffect(type);
            test.assertTrue(instance != null && instance.getDuration() == duration &&
                instance.getAmplifier() == amplifier && instance.isVisible() == visible &&
                instance.showIcon() == visible, "effect duration/amplifier/visibility on " + entity);
        }
    }

    static void run(GameTestHelper test) {
        var level = test.getLevel();
        var pos = Vec3.atBottomCenterOf(test.absolutePos(new BlockPos(1, 2, 1)));
        var source = level.getServer().createCommandSourceStack().withLevel(level).withPosition(pos);

        invoke(test, source, "here");
        result(test, 1);
        var markers = level.getEntities(EntityTypes.MARKER,
            e -> e.entityTags().isEmpty() && e.distanceToSqr(pos) < 0.001);
        test.assertTrue(markers.size() == 1, "summon here uses the execution position");
        var self = markers.getFirst();
        invoke(test, source, "at");
        result(test, 1);
        invoke(test, source, "empty");
        result(test, 1);
        test.assertTrue(level.getEntities(EntityTypes.PIG,
            e -> e.entityTags().isEmpty() && e.distanceToSqr(pos) < 0.001).size() == 2,
            "summon forms with omitted and explicit empty NBT both load");

        set(test, "#x", 2);
        set(test, "#age", -600);
        invoke(test, source, "dynamic");
        result(test, 1);
        var dynamic = level.getEntities(EntityTypes.PIG, e -> e.entityTags().contains("entitytest.dynamic"));
        test.assertTrue(dynamic.size() == 1, "summon dynamic NBT preserves tags");
        var pig = dynamic.getFirst();
        test.assertTrue(pig.getAge() == -600 && pig.getX() == pos.x + 2 &&
            pig.getY() == pos.y + 0.25 && pig.getZ() == pos.z - 0.5,
            "summon combines dynamic coordinates and NBT with static decimals");

        invoke(test, source, "snapshot");
        result(test, 1);
        var snapshots = level.getEntities(EntityTypes.PIG, e -> e.entityTags().contains("entitytest.snapshot"));
        test.assertTrue(snapshots.size() == 1 && snapshots.getFirst().getAge() == -900,
            "summon consumes a runtime compound snapshot");
        var passengers = level.getEntities(EntityTypes.MARKER, e -> e.entityTags().contains("entitytest.passenger"));
        test.assertTrue(passengers.size() == 1 && passengers.getFirst().getVehicle() == snapshots.getFirst(),
            "summon creates passengers and still returns one");

        invoke(test, source, "uuid");
        result(test, 1);
        invoke(test, source, "uuid");
        failed(test);
        test.assertTrue(level.getEntities(EntityTypes.MARKER,
            e -> e.entityTags().contains("entitytest.uuid")).size() == 1, "duplicate UUID leaves one entity");

        invoke(test, source, "prepare-effects");
        var affected = level.getEntities(EntityTypes.PIG, e -> e.entityTags().contains("entitytest.effects"));
        test.assertTrue(affected.size() == 2, "effect fixture has two living targets");
        invoke(test, source, "give");
        result(test, 2);
        effect(test, affected, MobEffects.SPEED, 600, 0, true);
        invoke(test, source, "give");
        failed(test);

        set(test, "#duration", 10);
        set(test, "#amplifier", 2);
        invoke(test, source, "give-dynamic");
        result(test, 2);
        effect(test, affected, MobEffects.WEAKNESS, 200, 2, false);
        set(test, "#duration", 0);
        invoke(test, source, "give-dynamic");
        failed(test);
        set(test, "#duration", 10);
        set(test, "#amplifier", 300);
        invoke(test, source, "give-dynamic");
        failed(test);
        effect(test, affected, MobEffects.WEAKNESS, 200, 2, false);

        invoke(test, source, "infinite");
        result(test, 2);
        effect(test, affected, MobEffects.NIGHT_VISION, -1, 0, true);
        invoke(test, source, "instant");
        result(test, 2);
        effect(test, affected, MobEffects.INSTANT_HEALTH, 1, 0, true);
        invoke(test, source, "instant-for");
        result(test, 2);
        effect(test, affected, MobEffects.INSTANT_HEALTH, 5, 0, true);

        invoke(test, source, "clear-one");
        result(test, 2);
        test.assertTrue(affected.stream().noneMatch(e -> e.hasEffect(MobEffects.SPEED)),
            "clear removes the selected effect");
        effect(test, affected, MobEffects.NIGHT_VISION, -1, 0, true);
        invoke(test, source, "clear-one");
        failed(test);
        invoke(test, source, "clear-all");
        result(test, 2);
        test.assertTrue(affected.stream().allMatch(e -> e.getActiveEffects().isEmpty()),
            "clear all counts changed entities, not removed effects");
        invoke(test, source, "clear-all");
        failed(test);
        invoke(test, source.withEntity(self), "self-effect");
        failed(test);
        invoke(test, source.withEntity(pig), "self-effect");
        result(test, 1);

        invoke(test, source, "prepare-kill");
        test.assertTrue(level.getEntities(EntityTypes.MARKER,
            e -> e.entityTags().contains("entitytest.temporary")).size() == 2, "kill fixture is populated");
        invoke(test, source, "kill");
        result(test, 2);
        invoke(test, source, "kill");
        failed(test);
        test.assertTrue(level.getEntities(EntityTypes.MARKER,
            e -> e.entityTags().contains("entitytest.temporary")).isEmpty(), "kill removes the selected entities");
        set(test, "#continued", 0);
        invoke(test, source, "stopping");
        score(test, "#continued", 0);
        invoke(test, source, "continuing");
        score(test, "#continued", 2);
        invoke(test, source.withEntity(self), "kill-self");
        result(test, 1);
        test.assertTrue(self.isRemoved(), "kill self completes result publication and frame cleanup");
    }
}
