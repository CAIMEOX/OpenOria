package oria.integration;

import net.minecraft.core.BlockPos;
import net.minecraft.core.component.DataComponents;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.world.Container;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.entity.EquipmentSlot;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.item.Items;
import net.minecraft.world.phys.Vec3;

import static oria.integration.BatchAcceptance.*;

final class ItemContentAcceptance {
    private static void reset(Container c) {
        c.clearContent();
        c.setItem(0, new ItemStack(Items.GOLD_INGOT, 1));
        c.setItem(1, new ItemStack(Items.GOLD_INGOT, 1));
        c.setItem(2, new ItemStack(Items.DIAMOND, 1));
    }

    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var p = t.absolutePos(new BlockPos(2, 8, 2));
        var level = t.getLevel();
        level.getChunkAt(p);
        level.getChunkAt(p.offset(12, 0, 8));
        for (int x = 0; x <= 12; ++x) for (int y = 0; y <= 3; ++y) for (int z = 0; z <= 8; ++z)
            level.setBlockAndUpdate(p.offset(x, y, z), net.minecraft.world.level.block.Blocks.AIR.defaultBlockState());
        var s = source(t).withPosition(Vec3.atLowerCornerOf(p));
        var self = s.withEntity(ada.entity());
        BlockContentAcceptance.run(t, s, p);
        var box = BlockContentAcceptance.chest(t, p);
        var actor = t.spawn(EntityTypes.PIG, new BlockPos(2, 10, 5));
        actor.addTag("content.actor");

        ada.entity().getInventory().clearContent();
        bob.entity().getInventory().clearContent();
        result(t, s, "giveApples", 2);
        result(t, s, "clearProbe", 6);
        result(t, s, "clearLimited", 2);
        result(t, s, "clearApples", 4);
        fail(t, s, "clearProbe");
        result(t, self, "giveNamed", 1);
        result(t, self, "clearNamed", 2);
        result(t, self, "clearData", 2);
        result(t, self, "clearCount", 2);
        result(t, self, "giveRemoved", 1);
        result(t, self, "clearNoFood", 1);
        result(t, self, "clearEither", 3);
        fail(t, self, "clearTag");
        set(t, "#input", 8);
        result(t, self, "giveComponentDynamic", 1);
        result(t, self, "componentNbt", 1);
        var inv = ada.entity().getInventory();
        boolean round8 = false, round9 = false;
        for (int i = 0; i < inv.getContainerSize(); ++i) {
            var data = inv.getItem(i).get(DataComponents.CUSTOM_DATA);
            if (data != null) {
                int round = data.copyTag().getInt("round").orElse(-1);
                round8 |= round == 8;
                round9 |= round == 9;
            }
        }
        t.assertTrue(round8 && round9, "mixed and runtime component NBT");
        set(t, "#input", 5);
        result(t, self, "giveDynamic", 1);
        set(t, "#input", 0);
        fail(t, self, "giveDynamic");
        set(t, "#input", -1);
        fail(t, self, "clearDynamic");
        set(t, "#input", 2);
        result(t, self, "clearDynamic", 2);
        ok(t, s, "clearAll");

        ada.entity().getInventory().setSelectedSlot(0);
        bob.entity().getInventory().setSelectedSlot(0);
        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, new ItemStack(Items.STONE, 2));
        ada.entity().setItemSlot(EquipmentSlot.OFFHAND, new ItemStack(Items.DIRT, 3));
        bob.entity().setItemSlot(EquipmentSlot.MAINHAND, new ItemStack(Items.GOLD_INGOT, 4));
        box.clearContent();
        ok(t, s, "itemSet");
        t.assertTrue(box.getItem(0).is(Items.APPLE) && box.getItem(0).getCount() == 4, "item with count");
        reset(box);
        ok(t, self, "itemReplace");
        t.assertTrue(box.getItem(0).is(Items.STONE) && box.getItem(1).is(Items.DIRT) &&
            box.getItem(2).is(Items.DIAMOND), "replace preserves unmatched slots");
        reset(box);
        ok(t, self, "itemFill");
        for (int i = 0; i < box.getContainerSize(); ++i)
            t.assertTrue(box.getItem(i).is(i % 2 == 0 ? Items.STONE : Items.DIRT), "fill repeats source entries");
        reset(box);
        ok(t, self, "itemOverride");
        t.assertTrue(box.getItem(0).is(Items.STONE) && box.getItem(1).is(Items.DIRT), "override prefix");
        for (int i = 2; i < box.getContainerSize(); ++i)
            t.assertTrue(box.getItem(i).isEmpty(), "override clears unmatched slots");
        reset(box);
        ok(t, self, "itemNamedSlots");
        t.assertTrue(box.getItem(1).is(Items.DIRT), "named slot source");
        reset(box);
        ok(t, self, "itemInlineSlots");
        t.assertTrue(box.getItem(1).is(Items.DIRT), "inline slot source");
        box.clearContent();
        ok(t, s, "itemSet");
        ok(t, self, "itemNamedModifier");
        t.assertTrue(box.getItem(0).getCount() == 6, "named item modifier");
        box.setItem(0, new ItemStack(Items.APPLE, 2));
        ok(t, self, "itemInlineModifier");
        t.assertTrue(box.getItem(0).getCount() == 6, "inline item modifier");
        ok(t, self, "itemModifiedCopy");
        t.assertTrue(box.getItem(1).is(Items.STONE) && box.getItem(1).getCount() == 4, "modified source copy");
        t.assertTrue(ada.entity().getMainHandItem().getCount() == 2, "copy does not mutate source inventory");
        set(t, "#input", 9);
        ok(t, s, "modifierDynamic");
        t.assertTrue(box.getItem(0).getCount() == 9, "typed dynamic modifier");
        set(t, "#input", 3);
        ok(t, s, "itemCountDynamic");
        t.assertTrue(box.getItem(0).getCount() == 3, "dynamic stack count");
        set(t, "#input", 4);
        ok(t, s, "itemSlotDynamic");
        t.assertTrue(box.getItem(4).is(Items.APPLE), "dynamic slot index");
        set(t, "#input", 99);
        fail(t, s, "itemSlotDynamic");
        fail(t, s, "itemBadSlot");
        ok(t, s, "itemEntity");
        t.assertTrue(ada.entity().getOffhandItem().is(Items.DIAMOND) &&
            bob.entity().getOffhandItem().getCount() == 2, "entity slot destinations");
        box.clearContent();
        ok(t, s, "itemEntitySource");
        t.assertTrue(box.getItem(0).is(Items.STONE) && box.getItem(1).is(Items.DIAMOND) &&
            box.getItem(2).is(Items.GOLD_INGOT) && box.getItem(3).is(Items.DIAMOND),
            "multi-entity sources concatenate slot sequences");

        ada.entity().getInventory().clearContent();
        bob.entity().getInventory().clearContent();
        result(t, self, "lootGive", 4);
        result(t, self, "lootInline", 1);
        box.clearContent();
        result(t, self, "lootInsert", 2);
        t.assertTrue(box.getItem(0).getCount() == 2 && box.getItem(1).getCount() == 3,
            "loot stack sizes retained: " + box.getItem(0) + ", " + box.getItem(1));
        box.setItem(2, new ItemStack(Items.DIAMOND));
        ok(t, self, "lootBlock");
        t.assertTrue(box.getItem(2).isEmpty(), "loot replacement clears remaining requested slots");
        ok(t, self, "lootEntity");
        t.assertTrue(ada.entity().getMainHandItem().is(Items.APPLE) &&
            ada.entity().getOffhandItem().is(Items.STICK), "loot replacement starts at one slot");
        var drop = new BlockPos(2, 9, 2);
        t.assertItemEntityCountIs(Items.APPLE, drop, 1, 0);
        t.assertItemEntityCountIs(Items.STICK, drop, 1, 0);
        result(t, self, "lootSpawn", 2);
        t.assertItemEntityCountIs(Items.APPLE, drop, 1, 2);
        t.assertItemEntityCountIs(Items.STICK, drop, 1, 3);
        result(t, self, "lootMine", 1);
        t.assertTrue(level.getBlockState(p.offset(3, 0, 0)).is(net.minecraft.world.level.block.Blocks.STONE),
            "mining loot does not destroy the block");
        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, new ItemStack(Items.DIAMOND_PICKAXE));
        result(t, self, "lootMineHeld", 1);
        ok(t, self, "lootKill");
        t.assertTrue(actor.isAlive(), "death-table evaluation does not kill the source");
        result(t, self, "lootFish", 2);
        set(t, "#input", 1);
        ok(t, self, "lootCountDynamic");
        actor.discard();
        ada.entity().getInventory().clearContent();
        bob.entity().getInventory().clearContent();
        ada.entity().setItemSlot(EquipmentSlot.OFFHAND, ItemStack.EMPTY);
        bob.entity().setItemSlot(EquipmentSlot.OFFHAND, ItemStack.EMPTY);
    }
}
