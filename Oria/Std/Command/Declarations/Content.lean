module

public import Oria.Std.Command.Arg.Block
public import Oria.Std.Command.Arg.Loot

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Declarations
open Oria.Std.Command.Arg
open Oria.Command (ArgCodec)

/-- Give described item stacks to players. -/
@[expose] public def giveItems : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ItemSpec), ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.giveItems
    template := .positional ["give"] }

/-- Clear matching items without a maximum count. -/
@[expose] public def clearItems : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ItemPredicate)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.clearItems
    template := .positional ["clear"] }

/-- Clear matching items or count them with limit zero. -/
@[expose] public def clearItemsLimit : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Players), ArgCodec.key (A := ItemPredicate), ArgCodec.key (A := Scalar)]
    req := Req.none
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.clearItemsLimit
    template := .positional ["clear"] }

/-- Distribute source stacks over selected inventory slots. -/
@[expose] public def transferItems : Oria.Command.Ref {
    schema := [ArgCodec.key (A := ItemDistribution), ArgCodec.key (A := Inventory), ArgCodec.key (A := ItemSource)]
    req := Req.dimension ||| Req.position
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.transferItems
    template := .positional ["item"] }

/-- Apply an item modifier to selected slots. -/
@[expose] public def modifyItems : Oria.Command.Ref {
    schema := [ArgCodec.key (A := Inventory), ArgCodec.key (A := ItemModifier)]
    req := Req.dimension ||| Req.position
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.modifyItems
    template := .positional ["item", "modify"] }

/-- Evaluate and distribute native loot. -/
@[expose] public def lootItems : Oria.Command.Ref {
    schema := [ArgCodec.key (A := LootTarget), ArgCodec.key (A := LootSource)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.lootItems
    template := .positional ["loot"] }

/-- Place one block and optional block-entity data. -/
@[expose] public def setBlock : Oria.Command.Ref {
    schema := [ArgCodec.key (A := BlockPos), ArgCodec.key (A := BlockState), ArgCodec.key (A := SetBlockMode)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.setBlock
    template := .positional ["setblock"] }

/-- Fill or filter an inclusive region. -/
@[expose] public def fillBlocks : Oria.Command.Ref {
    schema := [ArgCodec.key (A := BlockBox), ArgCodec.key (A := BlockState), ArgCodec.key (A := FillMode)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.fillBlocks
    template := .positional ["fill"] }

/-- Clone blocks with native dimension, filter, and mode settings. -/
@[expose] public def cloneBlocks : Oria.Command.Ref {
    schema := [ArgCodec.key (A := CloneSpec)]
    req := Req.dimension
    eff := Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  } := {
    key := `minecraft.std.cloneBlocks
    template := .positional ["clone"] }

/-- Item, inventory, loot, and block command declarations. -/
@[expose] public def content : List Oria.Command.Decl :=
  [giveItems.declaration,
    clearItems.declaration,
    clearItemsLimit.declaration,
    transferItems.declaration,
    modifyItems.declaration,
    lootItems.declaration,
    setBlock.declaration,
    fillBlocks.declaration,
    cloneBlocks.declaration]

end Oria.Std.Command.Declarations
