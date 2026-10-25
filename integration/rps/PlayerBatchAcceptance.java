package oria.integration;

import net.minecraft.core.BlockPos;
import net.minecraft.core.registries.Registries;
import net.minecraft.gametest.framework.GameTestHelper;
import net.minecraft.resources.Identifier;
import net.minecraft.resources.ResourceKey;
import net.minecraft.world.entity.EntityTypes;
import net.minecraft.world.entity.EquipmentSlot;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.item.Items;
import net.minecraft.world.item.enchantment.EnchantmentHelper;
import net.minecraft.world.level.GameType;

import static oria.integration.BatchAcceptance.*;

final class PlayerBatchAcceptance {
    private static boolean complete(GameTestHelper t, PlayerAcceptance.Player p, String id) {
        var advancement = t.getLevel().getServer().getAdvancements().get(Identifier.parse("batch:" + id));
        t.assertTrue(advancement != null, "fixture advancement " + id);
        return p.entity().getAdvancements().getOrStartProgress(advancement).isDone();
    }

    static void run(GameTestHelper t, PlayerAcceptance.Player ada, PlayerAcceptance.Player bob) {
        var s = source(t);
        var self = s.withEntity(ada.entity());
        ada.entity().setGameMode(GameType.SURVIVAL);
        result(t, self, "creative", 1);
        t.assertTrue(ada.entity().gameMode() == GameType.CREATIVE, "creative mode");
        result(t, self, "creative", 0);
        result(t, self, "survival", 1);
        ok(t, self, "xpLevels");
        result(t, self, "xpQueryLevels", 3);
        ok(t, self, "xpPoints");
        result(t, self, "xpQuery", 5);
        ok(t, self, "xpAdd");
        result(t, self, "xpQuery", 7);
        fail(t, self, "xpTooMany");
        set(t, "#input", -1);
        ok(t, self, "xpDynamic");
        result(t, self, "xpQueryLevels", 2);
        result(t, s, "recipeGive", 2);
        fail(t, s, "recipeGive");
        result(t, s, "recipeTake", 2);
        fail(t, s, "recipeTake");
        ok(t, s, "recipeAll");
        ok(t, s, "recipeTakeAll");

        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, ItemStack.EMPTY);
        fail(t, self, "enchant");
        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, new ItemStack(Items.DIAMOND_SWORD));
        result(t, self, "enchant", 1);
        var sharpness = t.getLevel().registryAccess().lookupOrThrow(Registries.ENCHANTMENT)
            .getOrThrow(ResourceKey.create(Registries.ENCHANTMENT, Identifier.parse("minecraft:sharpness")));
        t.assertTrue(EnchantmentHelper.getItemEnchantmentLevel(sharpness, ada.entity().getMainHandItem()) == 1,
            "native enchantment applied");
        set(t, "#input", 100);
        fail(t, self, "enchantDynamic");

        for (String name : new String[]{"damage", "damageType", "damageAt", "damageBy", "damageFrom"}) {
            var pig = t.spawn(EntityTypes.PIG, new BlockPos(1, 2, 1));
            pig.addTag("batch.victim");
            var health = pig.getHealth();
            result(t, self, name, 1);
            t.assertTrue(pig.getHealth() < health, name + " changes health");
            pig.discard();
        }
        var pig = t.spawn(EntityTypes.PIG, new BlockPos(1, 2, 1));
        pig.addTag("batch.victim");
        set(t, "#input", -1);
        fail(t, self, "damageDynamic");
        pig.setPermanentlyInvulnerable(true);
        fail(t, self, "damage");
        pig.discard();

        set(t, "#reward", 0);
        result(t, s, "grantCriterion", 2);
        t.assertFalse(complete(t, ada, "root"), "one criterion does not complete the root");
        result(t, s, "grantOnly", 2);
        t.assertTrue(complete(t, ada, "root") && complete(t, bob, "root"), "root granted");
        t.assertTrue(score(t, "#reward") == 2, "native reward function executed once per player");
        fail(t, s, "grantOnly");
        ok(t, s, "grantFrom");
        t.assertTrue(complete(t, ada, "child") && complete(t, ada, "leaf"), "descendants granted");
        ok(t, s, "revokeThrough");
        t.assertFalse(complete(t, ada, "root") || complete(t, ada, "child") || complete(t, ada, "leaf"),
            "through scope revokes the chain");
        ok(t, s, "grantUntil");
        t.assertTrue(complete(t, ada, "root") && complete(t, ada, "child") && !complete(t, ada, "leaf"),
            "until scope grants ancestors only");
        ok(t, s, "revokeEverything");
        ok(t, s, "grantThrough");
        t.assertTrue(complete(t, ada, "leaf"), "through scope grants descendants");
        ok(t, s, "revokeCriterion");
        t.assertFalse(complete(t, ada, "root"), "criterion revocation");
        ok(t, s, "revokeFrom");
        ada.entity().setItemSlot(EquipmentSlot.MAINHAND, ItemStack.EMPTY);
    }
}
