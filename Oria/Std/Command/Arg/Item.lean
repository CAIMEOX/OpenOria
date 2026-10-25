module

public import Oria.Std.Command.Arg.Registry
public import Oria.Std.Command.Arg.Position

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Item and inventory arguments

ItemSpec describes a native item ID and its component patch. ItemPredicate describes
matching, including conjunctions of alternative component tests. Values are SNBT fragments,
so static NBT and typed numeric holes use the existing serialization algebra.

Item commands use SlotSource, which can select several slots. Loot replacement uses Slot,
which names one starting slot. Native parsers check slot availability and registry schemas.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode Fragment)

/-- A patch to the native components of a constructed item. -/
public inductive ComponentPatch where
  /-- Set a component to an SNBT value. -/
  | set : ResourceId → Oria.Command.Fragment EncodedVal → ComponentPatch
  /-- Remove a default component. -/
  | remove : ResourceId → ComponentPatch

/-- Serialize a host component value through ToNbt. -/
@[expose] public def ComponentPatch.ofNbt {a : Type u} [Nbt.ToNbt a]
    (id : ResourceId) (value : a) : ComponentPatch :=
  .set id (.nbt (Nbt.ToNbt.toNbt value).2)

/-- Encode one component assignment or removal. -/
@[expose] public def ComponentPatch.fragment : ComponentPatch → Oria.Command.Fragment EncodedVal
  | .set id v => (encode id).fragment.append ((Fragment.token "=").append v)
  | .remove id => .prepend "!" (encode id).fragment

/-- Native item construction. Count belongs to the receiving command. -/
public structure ItemSpec where
  /-- Registered item type. -/
  id : ResourceId
  /-- Component assignments and removals; duplicate IDs are rejected by Minecraft. -/
  components : List ComponentPatch := []

public instance : Oria.Command.ArgCodec ItemSpec where
  key := ⟨`minecraft.argument.item_stack⟩
  encode item :=
    let patch : Fragment EncodedVal := match item.components with
      | [] => .empty
      | xs => (Fragment.token "[").append
          (((xs.map ComponentPatch.fragment).intersperse (Fragment.token ",")).foldl Fragment.append Fragment.empty
            |>.append (Fragment.token "]"))
    (encode item.id).fragment.append patch

/-- Context dependencies of dynamic component fragments. -/
@[expose] public def ItemSpec.requirements (item : ItemSpec) : ReqRow := (encode item).requirements

/-- One disjunctive component condition. A predicate's list of conditions is conjunctive. -/
public inductive ItemTest where
  /-- Test component presence, optionally negated. -/
  | present (id : ResourceId) (negated : Bool := false)
  /-- Compare the complete component value using native equality. -/
  | equal (id : ResourceId) (value : Oria.Command.Fragment EncodedVal) (negated : Bool := false)
  /-- Apply a registered component sub-predicate, such as custom-data or count matching. -/
  | matches (id : ResourceId) (value : Oria.Command.Fragment EncodedVal) (negated : Bool := false)
  /-- Disjunction inside one condition. -/
  | either : ItemTest → ItemTest → ItemTest

/-- Encode one disjunctive native component condition. -/
@[expose] public def ItemTest.fragment : ItemTest → Oria.Command.Fragment EncodedVal
  | .present id negated =>
      let f := (encode id).fragment
      if negated then .prepend "!" f else f
  | .equal id value negated =>
      let f := (encode id).fragment.append ((Fragment.token "=").append value)
      if negated then .prepend "!" f else f
  | .matches id value negated =>
      let f := (encode id).fragment.append ((Fragment.token "~").append value)
      if negated then .prepend "!" f else f
  | .either l r => (ItemTest.fragment l).append ((Fragment.token "|").append (ItemTest.fragment r))

/-- Item/tag/wildcard selection with native component conditions. -/
public structure ItemPredicate where
  /-- None selects every item type; some selects one type or tag. -/
  target : Option Oria.Command.ResourceOrTag := none
  /-- Comma-separated conditions. Each condition may contain alternatives. -/
  tests : List ItemTest := []

public instance : Oria.Command.ArgCodec ItemPredicate where
  key := ⟨`minecraft.argument.item_predicate⟩
  encode p :=
    let head : Fragment EncodedVal := p.target.map (fun t => (encode t).fragment) |>.getD (Fragment.token "*")
    let conditions : Fragment EncodedVal := match p.tests with
      | [] => .empty
      | xs => (Fragment.token "[").append
          (((xs.map ItemTest.fragment).intersperse (Fragment.token ",")).foldl Fragment.append Fragment.empty
            |>.append (Fragment.token "]"))
    head.append conditions

/-- Dependencies of dynamic SNBT predicate values. -/
@[expose] public def ItemPredicate.requirements (p : ItemPredicate) : ReqRow := (encode p).requirements

/-- One native inventory slot. -/
public inductive Slot where
  /-- Static slot name, such as weapon.mainhand or container.0. -/
  | named : Oria.Command.Word → Slot
  /-- Named slot group with a static or dynamic integer index. -/
  | indexed : Oria.Command.Word → Scalar → Slot

public instance : Oria.Command.ArgCodec Slot where
  key := ⟨`minecraft.argument.slot⟩
  encode slot :=
    let f : Fragment EncodedVal := match slot with
      | .named name => (encode name).fragment
      | .indexed group i => (encode group).fragment.append ((Fragment.token ".").append (encode i).fragment)
    ⟨f.segments, Req.none⟩

@[simp] public theorem Slot.encode_requirements (s : Slot) : (encode s).requirements = Req.none := rfl

/-- Literal, dynamic-indexed, or registry-defined slot selection. -/
public inductive SlotSource where
  /-- Native literal range, such as the container wildcard or weapon.mainhand. -/
  | range : Oria.Command.SyntaxToken → SlotSource
  /-- One possibly dynamic slot. -/
  | single : Slot → SlotSource
  /-- Evaluate a named or inline slot-source definition. -/
  | defined : SlotDefinition → SlotSource

public instance : Oria.Command.ArgCodec SlotSource where
  key := ⟨`minecraft.argument.slot_source⟩
  encode
    | .range s => .token s
    | .single s => (encode s).fragment
    | .defined d => (encode d).fragment

/-- Additional dependencies beyond the native slot context. -/
@[expose] public def SlotSource.requirements (s : SlotSource) : ReqRow := (encode s).requirements

/-- Native location capable of exposing inventory slots. -/
public inductive InventoryTarget where
  /-- A loaded block with an inventory. -/
  | block : BlockPos → InventoryTarget
  /-- Selected entities with appropriate native slots. -/
  | entity : Target → InventoryTarget

public instance : Oria.Command.ArgCodec InventoryTarget where
  key := ⟨`minecraft.argument.inventory_target⟩
  encode
    | .block p => .require Req.dimension (.spaced [.token "block", (encode p).fragment])
    | .entity t => .spaced [.token "entity", (encode t).fragment]

/-- Inventory location plus its selected slots. -/
public structure Inventory where
  /-- Source or destination location. -/
  target : InventoryTarget
  /-- Slots selected within each location. -/
  slots : SlotSource

public instance : Oria.Command.ArgCodec Inventory where
  key := ⟨`minecraft.argument.inventory⟩
  encode v := .spaced [(encode v.target).fragment, (encode v.slots).fragment]

/-- Inventory and slot-source dependencies. -/
@[expose] public def Inventory.requirements (v : Inventory) : ReqRow := (encode v).requirements

/-- Input to a native item transfer. -/
public inductive ItemSource where
  /-- Construct one stack, whose count must be accepted by the native item parser. -/
  | stack : ItemSpec → Scalar → ItemSource
  /-- Read selected inventory slots, optionally applying an item modifier. -/
  | from : Inventory → Option ItemModifier → ItemSource

public instance : Oria.Command.ArgCodec ItemSource where
  key := ⟨`minecraft.argument.item_source⟩
  encode
    | .stack item count => .spaced [.token "with", (encode item).fragment, (encode count).fragment]
    | .from source modifier => .spaced
        ([.token "from", (encode source).fragment] ++
          modifier.toList.map (fun m => (encode m).fragment))

/-- Source inventory, component, and modifier dependencies. -/
@[expose] public def ItemSource.requirements (s : ItemSource) : ReqRow := (encode s).requirements

/-- Distribution of source stacks across destination slots. -/
public inductive ItemDistribution where
  /-- Copy corresponding source entries, leaving the unmatched destination suffix alone. -/
  | replace
  /-- Repeat source entries to fill all selected destination slots. -/
  | fill
  /-- Copy corresponding entries and clear the unmatched destination suffix. -/
  | override

public instance : Oria.Command.ArgCodec ItemDistribution where
  key := ⟨`minecraft.argument.item_distribution⟩
  encode d := .token (match d with | .replace => "replace" | .fill => "fill" | .override => "override")

@[simp] public theorem ItemDistribution.encode_requirements (d : ItemDistribution) :
    (encode d).requirements = Req.none := rfl

end Oria.Std.Command.Arg
