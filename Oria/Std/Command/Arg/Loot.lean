module

public import Oria.Std.Command.Arg.Item
public import Oria.Std.Command.Arg.Control

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Loot sources and destinations

Loot evaluation and distribution are independent arguments. Native loot replacement starts
at one Slot and optionally supplies a count; item transfers use multi-slot SlotSource.
Registered and inline loot tables use the same typed registry description.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode Fragment)

/-- Tool used for native mining and fishing loot contexts. -/
public inductive LootTool where
  /-- Native empty tool, emitted by omitting the argument. -/
  | empty
  /-- One explicitly described tool stack. -/
  | item : ItemSpec → LootTool
  /-- Item held by the execution entity; the entity must be living. -/
  | held : Hand → LootTool

/-- Encode a mining or fishing tool, retaining executor requirements for held items. -/
@[expose] public def LootTool.fragment : LootTool → Oria.Command.Fragment EncodedVal
  | .empty => .empty
  | .item v => (encode v).fragment
  | .held hand => .require Req.executor (encode hand).fragment

/-- Native origin of generated loot. This does not destroy blocks or kill entities. -/
public inductive LootSource where
  /-- Evaluate a loot table in the command chest-loot context. -/
  | table : LootTable → LootSource
  /-- Evaluate a living entity's death loot table without killing it. -/
  | kill : Target → LootSource
  /-- Evaluate a loaded block's drops without removing the block. -/
  | mine : BlockPos → LootTool → LootSource
  /-- Evaluate a fishing table at a loaded block position. -/
  | fish : LootTable → BlockPos → LootTool → LootSource

public instance : Oria.Command.ArgCodec LootSource where
  key := ⟨`minecraft.argument.loot_source⟩
  encode
    | .table table => .spaced [.token "loot", (encode table).fragment]
    | .kill target => .require Req.all (.spaced [.token "kill", (encode target).fragment])
    | .mine p tool => .require Req.all
        (.spaced [.token "mine", (encode p).fragment, LootTool.fragment tool])
    | .fish table p tool => .spaced
        [.token "fish", (encode table).fragment, (encode p).fragment, LootTool.fragment tool]

/-- Dependencies of external loot-table evaluation and source selection. -/
@[expose] public def LootSource.requirements (s : LootSource) : ReqRow := (encode s).requirements

/-- Native loot distribution destination. -/
public inductive LootTarget where
  /-- Give generated stacks to selected players. -/
  | give : Players → LootTarget
  /-- Spawn item entities at a position. -/
  | spawn : Vec3 → LootTarget
  /-- Merge into available slots in a block inventory. -/
  | insert : BlockPos → LootTarget
  /-- Replace consecutive slots, starting at one Slot. None uses the generated stack count. -/
  | replace : InventoryTarget → Slot → Option Scalar → LootTarget

public instance : Oria.Command.ArgCodec LootTarget where
  key := ⟨`minecraft.argument.loot_target⟩
  encode
    | .give players => .spaced [.token "give", (encode players).fragment]
    | .spawn p => .require Req.dimension (.spaced [.token "spawn", (encode p).fragment])
    | .insert p => .require Req.dimension (.spaced [.token "insert", (encode p).fragment])
    | .replace target slot count => .spaced
        ([.token "replace", (encode target).fragment, (encode slot).fragment] ++
          count.toList.map (fun n => (encode n).fragment))

/-- Destination-selection and coordinate requirements. -/
@[expose] public def LootTarget.requirements (t : LootTarget) : ReqRow := (encode t).requirements

end Oria.Std.Command.Arg
