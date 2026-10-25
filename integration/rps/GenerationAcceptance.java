package oria.integration;

import java.util.ArrayList;
import java.util.List;
import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Vec3i;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.Stopwatch;
import net.minecraft.world.Stopwatches;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.item.Items;
import net.minecraft.world.level.biome.Biomes;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.block.Mirror;
import net.minecraft.world.level.block.Rotation;
import net.minecraft.world.level.block.entity.JigsawBlockEntity;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.level.levelgen.structure.templatesystem.StructureTemplate;
import net.minecraft.world.phys.Vec3;
import net.minecraft.world.waypoints.WaypointStyleAssets;

import static oria.integration.BatchAcceptance.score;
import static oria.integration.BatchAcceptance.set;

/** Generated entries exercise native biome cells, placement, waypoint icons, and real-time clocks. */
final class GenerationAcceptance {
    private static void invoke(GameTestHelper t, CommandSourceStack s, String name) {
        set(t, "#status", -1);
        PlayerAcceptance.command(t, s, "function generation:" + name.toLowerCase());
        PlayerAcceptance.clean(t, "generation");
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

    private static void clearTemplate(GameTestHelper t, BlockPos p) {
        for (int x = -2; x <= 2; ++x) for (int z = -2; z <= 2; ++z)
            t.getLevel().setBlockAndUpdate(p.offset(x, 0, z), Blocks.AIR.defaultBlockState());
    }

    private static List<BlockState> footprint(GameTestHelper t, BlockPos p) {
        var out = new ArrayList<BlockState>();
        for (int x = -2; x <= 2; ++x) for (int z = -2; z <= 2; ++z)
            out.add(t.getLevel().getBlockState(p.offset(x, 0, z)));
        return out;
    }

    private static void template(GameTestHelper t, CommandSourceStack s, BlockPos p,
            String name, Rotation rotation, Mirror mirror) {
        clearTemplate(t, p);
        result(t, s, name, 1);
        var gold = StructureTemplate.transform(new BlockPos(1, 0, 0), mirror, rotation, BlockPos.ZERO);
        var log = StructureTemplate.transform(new BlockPos(0, 0, 1), mirror, rotation, BlockPos.ZERO);
        t.assertTrue(t.getLevel().getBlockState(p.offset(gold)).is(Blocks.GOLD_BLOCK), name + " gold position");
        t.assertTrue(t.getLevel().getBlockState(p.offset(log)).is(Blocks.OAK_LOG), name + " log position");
        var chest = BlockContentAcceptance.chest(t, p);
        t.assertTrue(chest.getItem(0).is(Items.DIAMOND) && chest.getItem(0).getCount() == 5,
            name + " preserves template block-entity NBT");
    }

    private static void placement(GameTestHelper t, CommandSourceStack s, BlockPos p) {
        var level = t.getLevel();
        // Feature placement requires the origin's complete 3 by 3 chunk neighborhood.
        for (int x = -32; x <= 112; x += 16) for (int z = -32; z <= 32; z += 16)
            level.getChunkAt(p.offset(x, 0, z));
        clearTemplate(t, p);
        result(t, s, "featureNamed", 1);
        t.assertTrue(level.getBlockState(p).is(Blocks.GOLD_BLOCK), "named feature output");
        result(t, s, "featureInline", 1);
        t.assertTrue(level.getBlockState(p.offset(1, 0, 0)).is(Blocks.DIAMOND_BLOCK), "inline feature output");
        level.setBlockAndUpdate(p, Blocks.AIR.defaultBlockState());
        level.setBlockAndUpdate(p.below(), Blocks.STONE.defaultBlockState());
        fail(t, s, "featureFailure");
        set(t, "#input", 5);
        result(t, s, "featureDynamic", 1);
        t.assertTrue(level.getBlockState(p.offset(5, 0, 0)).is(Blocks.GOLD_BLOCK), "dynamic feature position");

        var q = p.offset(16, 0, 16);
        level.setBlockAndUpdate(q, Blocks.CHEST.defaultBlockState());
        BlockContentAcceptance.chest(t, q).setItem(0, new ItemStack(Items.DIAMOND, 5));
        level.setBlockAndUpdate(q.offset(1, 0, 0), Blocks.GOLD_BLOCK.defaultBlockState());
        level.setBlockAndUpdate(q.offset(0, 0, 1), Blocks.OAK_LOG.defaultBlockState());
        level.setBlockAndUpdate(q.offset(1, 0, 1), Blocks.AIR.defaultBlockState());
        var templates = level.getStructureTemplateManager();
        templates.getOrCreate(Identifier.parse("generation:template"))
            .fillFromWorld(level, q, new Vec3i(2, 1, 2), false, List.of());
        template(t, s, p, "template", Rotation.NONE, Mirror.NONE);
        template(t, s, p, "template90", Rotation.CLOCKWISE_90, Mirror.NONE);
        template(t, s, p, "template180", Rotation.CLOCKWISE_180, Mirror.NONE);
        template(t, s, p, "template270", Rotation.COUNTERCLOCKWISE_90, Mirror.NONE);
        template(t, s, p, "templateMirrorX", Rotation.NONE, Mirror.FRONT_BACK);
        template(t, s, p, "templateMirrorZ", Rotation.NONE, Mirror.LEFT_RIGHT);
        template(t, s, p, "templateStrict", Rotation.NONE, Mirror.NONE);
        clearTemplate(t, p);
        result(t, s, "templateZero", 1);
        t.assertTrue(footprint(t, p).stream().allMatch(BlockState::isAir), "zero integrity can succeed without blocks");
        clearTemplate(t, p);
        result(t, s, "templateSeeded", 1);
        var first = footprint(t, p);
        clearTemplate(t, p);
        result(t, s, "templateSeeded", 1);
        t.assertTrue(first.equals(footprint(t, p)), "explicit seed repeats the retention pattern");
        clearTemplate(t, p);
        set(t, "#input", 1);
        result(t, s, "templateDynamic", 1);
        t.assertTrue(level.getBlockState(p.offset(1, 0, 0)).is(Blocks.GOLD_BLOCK), "dynamic integrity and seed");
        set(t, "#input", 2);
        fail(t, s, "templateDynamic");
        fail(t, s, "templateMissing");

        var j = q.offset(4, 0, 0);
        level.setBlockAndUpdate(j, Blocks.JIGSAW.defaultBlockState());
        var connector = (JigsawBlockEntity) level.getBlockEntity(j);
        connector.setName(Identifier.parse("generation:start"));
        connector.setTarget(Identifier.parse("minecraft:empty"));
        connector.setPool(ResourceKey.create(Registries.TEMPLATE_POOL, Identifier.parse("minecraft:empty")));
        connector.setFinalState("minecraft:emerald_block");
        templates.getOrCreate(Identifier.parse("generation:jigsaw_start"))
            .fillFromWorld(level, j, new Vec3i(1, 1, 1), false, List.of());
        result(t, s, "jigsaw", 1);
        boolean emerald = false;
        for (var pos : BlockPos.betweenClosed(p.offset(5, -3, -3), p.offset(11, 3, 3)))
            emerald |= level.getBlockState(pos).is(Blocks.EMERALD_BLOCK);
        t.assertTrue(emerald, "jigsaw materializes its connector's final state");
        fail(t, s, "jigsawAbsent");
        set(t, "#input", 1);
        result(t, s, "jigsawDynamic", 1);
        set(t, "#input", 0);
        fail(t, s, "jigsawDynamic");
        result(t, s, "structure", 1);
    }

    private static void biomes(GameTestHelper t, CommandSourceStack s, BlockPos p) {
        var level = t.getLevel();
        var registry = level.registryAccess().lookupOrThrow(Registries.BIOME);
        net.minecraft.server.commands.FillBiomeCommand.fill(level, p, p.offset(7, 7, 7),
            registry.getOrThrow(Biomes.THE_VOID));
        result(t, s, "biomeCube", 8);
        fail(t, s, "biomeCube");
        result(t, s, "biomeSingle", 1);
        t.assertTrue(level.getNoiseBiome(p.getX() >> 2, p.getY() >> 2, p.getZ() >> 2).is(Biomes.DESERT),
            "corners inside one quart cell update one biome sample");
        result(t, s, "biomeFiltered", 7);
        fail(t, s, "biomeFiltered");
        result(t, s, "biomeTag", 7);
        fail(t, s, "biomeNoMatch");
        fail(t, s, "biomeTooLarge");
        set(t, "#input", 7);
        result(t, s, "biomeDynamic", 8);
    }

    private static void waypoints(GameTestHelper t, CommandSourceStack s, PlayerAcceptance.Player ada) {
        var self = s.withEntity(ada.entity());
        result(t, s, "waypointList", t.getLevel().getWaypointManager().transmitters().size());
        result(t, self, "waypointRed", 0);
        t.assertTrue((ada.entity().waypointIcon().color.orElseThrow() & 0xffffff) == 0xff5555, "named waypoint color");
        result(t, self, "waypointRed", 0);
        result(t, self, "waypointHex", 0);
        t.assertTrue((ada.entity().waypointIcon().color.orElseThrow() & 0xffffff) == 0x6495ed, "six-digit waypoint color");
        result(t, self, "waypointShortHex", 0);
        t.assertTrue((ada.entity().waypointIcon().color.orElseThrow() & 0xffffff) == 0xff00aa, "three-digit waypoint color");
        result(t, self, "waypointColorReset", 0);
        t.assertTrue(ada.entity().waypointIcon().color.isEmpty(), "automatic waypoint color");
        result(t, self, "waypointStyle", 0);
        t.assertTrue(ada.entity().waypointIcon().style.equals(WaypointStyleAssets.BOWTIE), "waypoint style");
        result(t, self, "waypointStyleReset", 0);
        t.assertTrue(ada.entity().waypointIcon().style.equals(WaypointStyleAssets.DEFAULT), "default waypoint style");
        var marker = t.spawn(EntityTypes.MARKER, new BlockPos(2, 16, 2));
        fail(t, s.withEntity(marker), "waypointRed");
        marker.discard();
        var pig = t.spawn(EntityTypes.PIG, new BlockPos(3, 16, 2));
        t.assertFalse(pig.isTransmittingWaypoint(), "pig initially has zero transmission range");
        result(t, s.withEntity(pig), "waypointRed", 0);
        t.assertTrue(pig.waypointIcon().color.isPresent(), "modify accepts an untracked transmitter");
        pig.discard();
        fail(t, s, "waypointMissing");
    }

    private static void clock(GameTestHelper t, CommandSourceStack s, String name, double scale) {
        var watch = t.getLevel().getServer().getStopwatches().get(Identifier.parse("generation:lap"));
        int before = (int)(watch.elapsedSeconds(Stopwatches.currentTime()) * scale);
        int actual = ok(t, s, name);
        int after = (int)(watch.elapsedSeconds(Stopwatches.currentTime()) * scale);
        t.assertTrue(Math.min(before, after) <= actual && actual <= Math.max(before, after),
            name + " native elapsed-time interval [" + before + "," + after + "], got " + actual);
    }

    private static void stopwatches(GameTestHelper t, CommandSourceStack s) {
        var clocks = t.getLevel().getServer().getStopwatches();
        var id = Identifier.parse("generation:lap");
        fail(t, s, "watchQuery");
        fail(t, s, "watchRestart");
        fail(t, s, "watchRemove");
        result(t, s, "watchCreate", 1);
        var original = clocks.get(id);
        fail(t, s, "watchCreate");
        t.assertTrue(clocks.get(id).equals(original), "duplicate creation retains the stopwatch");
        clocks.update(id, old -> new Stopwatch(Stopwatches.currentTime(), 12345));
        clock(t, s, "watchQuery", 1);
        clock(t, s, "watchMillis", 1000);
        clock(t, s, "watchFraction", 0.5);
        clock(t, s, "watchNegative", -1000);
        result(t, s, "watchZero", 0);
        set(t, "#input", 100);
        clock(t, s, "watchDynamic", 100);
        result(t, s, "watchRestart", 1);
        t.assertTrue(clocks.get(id).accumulatedElapsedTime() == 0, "restart clears accumulated time");
        result(t, s, "watchRemove", 1);
        fail(t, s, "watchQuery");
    }

    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var base = t.absolutePos(new BlockPos(2, 32, 2));
        var p = new BlockPos(base.getX() & -4, base.getY() & -4, base.getZ() & -4);
        var s = BatchAcceptance.source(t).withPosition(Vec3.atLowerCornerOf(p));
        for (int x : new int[]{0, 7}) for (int z : new int[]{0, 7})
            t.getLevel().getChunkAt(p.offset(x, 0, z));
        biomes(t, s, p);
        placement(t, s, p);
        waypoints(t, s, ada);
        stopwatches(t, s);
    }
}
