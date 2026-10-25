package oria.integration;

import net.minecraft.commands.CommandSourceStack;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.world.Container;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.item.Items;
import net.minecraft.world.level.Level;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.block.ChestBlock;
import net.minecraft.world.level.block.LightBlock;
import net.minecraft.world.level.block.RotatedPillarBlock;

import static oria.integration.BatchAcceptance.*;

final class BlockContentAcceptance {
    static Container chest(GameTestHelper t, BlockPos p) {
        var entity = t.getLevel().getBlockEntity(p);
        t.assertTrue(entity instanceof Container, "expected native block inventory at " + p);
        return (Container) entity;
    }

    private static void row(GameTestHelper t, BlockPos p) {
        var level = t.getLevel();
        level.setBlockAndUpdate(p.offset(3, 0, 0), Blocks.STONE.defaultBlockState());
        level.setBlockAndUpdate(p.offset(4, 0, 0), Blocks.OAK_PLANKS.defaultBlockState());
        level.setBlockAndUpdate(p.offset(5, 0, 0), Blocks.AIR.defaultBlockState());
        for (int x = 8; x <= 10; ++x)
            level.setBlockAndUpdate(p.offset(x, 0, 0), Blocks.DIRT.defaultBlockState());
    }

    static void run(GameTestHelper t, CommandSourceStack s, BlockPos p) {
        var level = t.getLevel();
        result(t, s, "placeChest", 1);
        var box = chest(t, p);
        box.setItem(0, new ItemStack(Items.DIAMOND, 5));
        result(t, s, "turnChest", 1);
        t.assertTrue(chest(t, p).getItem(0).is(Items.DIAMOND) &&
            level.getBlockState(p).getValue(ChestBlock.FACING) == Direction.EAST,
            "omitted NBT preserves inventory across a state change");
        result(t, s, "clearChestData", 1);
        t.assertTrue(chest(t, p).isEmpty(), "explicit empty NBT clears inventory");
        chest(t, p).setItem(0, new ItemStack(Items.DIAMOND, 5));
        result(t, s, "blockNbt", 1);
        t.assertTrue(chest(t, p).isEmpty(), "runtime compound NBT clears inventory");
        chest(t, p).setItem(0, new ItemStack(Items.DIAMOND, 5));
        result(t, s, "cloneChest", 1);
        t.assertTrue(chest(t, p.offset(1, 0, 0)).getItem(0).getCount() == 5, "cloned block inventory");
        chest(t, p).clearContent();
        t.assertTrue(chest(t, p.offset(1, 0, 0)).getItem(0).getCount() == 5, "cloned data is independent");

        result(t, s, "placeStone", 1);
        fail(t, s, "placeKeep");
        result(t, s, "placeDestroy", 1);
        result(t, s, "placeStrict", 1);
        result(t, s, "fillStone", 2);
        fail(t, s, "fillStone");
        result(t, s, "fillFiltered", 3);
        result(t, s, "fillTag", 3);
        fail(t, s, "fillKeep");
        result(t, s, "fillDestroy", 3);
        level.setBlockAndUpdate(p.offset(3, 0, 0),
            Blocks.OAK_LOG.defaultBlockState().setValue(RotatedPillarBlock.AXIS, Direction.Axis.X));
        level.setBlockAndUpdate(p.offset(4, 0, 0), Blocks.OAK_LOG.defaultBlockState());
        result(t, s, "fillProperties", 1);
        t.assertTrue(level.getBlockState(p.offset(4, 0, 0)).is(Blocks.OAK_LOG), "property filter retains other states");
        result(t, s, "fillCube", 27);
        result(t, s, "fillOutline", 26);
        t.assertTrue(level.getBlockState(p.offset(1, 1, 5)).is(Blocks.STONE), "outline preserves interior");
        ok(t, s, "fillHollow");
        t.assertTrue(level.getBlockState(p.offset(1, 1, 5)).isAir(), "hollow clears interior");

        row(t, p);
        ok(t, s, "cloneNormal");
        t.assertTrue(level.getBlockState(p.offset(8, 0, 0)).is(Blocks.STONE) &&
            level.getBlockState(p.offset(9, 0, 0)).is(Blocks.OAK_PLANKS) &&
            level.getBlockState(p.offset(10, 0, 0)).isAir(), "clone copies source air");
        row(t, p);
        result(t, s, "cloneMasked", 2);
        t.assertTrue(level.getBlockState(p.offset(10, 0, 0)).is(Blocks.DIRT), "masked clone skips air");
        row(t, p);
        result(t, s, "cloneFiltered", 1);
        t.assertTrue(level.getBlockState(p.offset(8, 0, 0)).is(Blocks.DIRT) &&
            level.getBlockState(p.offset(9, 0, 0)).is(Blocks.OAK_PLANKS), "strict filtered clone");
        fail(t, s, "cloneOverlap");
        ok(t, s, "cloneForce");
        t.assertTrue(level.getBlockState(p.offset(4, 0, 0)).is(Blocks.STONE) &&
            level.getBlockState(p.offset(5, 0, 0)).is(Blocks.OAK_PLANKS), "force clones overlap from a snapshot");
        row(t, p);
        ok(t, s, "cloneMove");
        for (int x = 3; x <= 5; ++x)
            t.assertTrue(level.getBlockState(p.offset(x, 0, 0)).isAir(), "move clears source");
        row(t, p);
        ok(t, s, "cloneDimensions");
        var nether = level.getServer().getLevel(Level.NETHER);
        var destination = new BlockPos(0, 64, 0);
        nether.getChunkAt(destination);
        var old = new net.minecraft.world.level.block.state.BlockState[3];
        for (int x = 0; x < 3; ++x) old[x] = nether.getBlockState(destination.offset(x, 0, 0));
        ok(t, s, "cloneCrossDimension");
        t.assertTrue(nether.getBlockState(destination).is(Blocks.STONE) &&
            nether.getBlockState(destination.offset(1, 0, 0)).is(Blocks.OAK_PLANKS), "cross-dimension clone");
        for (int x = 0; x < 3; ++x) nether.setBlockAndUpdate(destination.offset(x, 0, 0), old[x]);

        set(t, "#input", 7);
        result(t, s, "propertyDynamic", 1);
        t.assertTrue(level.getBlockState(p.offset(3, 0, 0)).getValue(LightBlock.LEVEL) == 7,
            "dynamic block property");
        set(t, "#input", 16);
        fail(t, s, "propertyDynamic");
        for (int x = 3; x <= 5; ++x) level.setBlockAndUpdate(p.offset(x, 0, 0), Blocks.AIR.defaultBlockState());
        set(t, "#input", 5);
        result(t, s, "fillDynamic", 3);
        set(t, "#input", 40000);
        fail(t, s, "fillDynamic");
        chest(t, p).clearContent();
    }
}
