module

public import Oria.Std.Command.Arg.Registry
public import Oria.Std.Command.Arg.Position

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Block descriptions

Concrete block states and block predicates share property and NBT suffixes. Their head types
distinguish one block ID from an ID-or-tag match. Omitting block-entity NBT is different from
supplying an empty compound. Minecraft validates property names, values, and block entities.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode Fragment ResourceOrTag)

/-- Property values supplied as native words or computed integers. -/
public inductive BlockProperty where
  /-- Native enum, Boolean, or numeric spelling. -/
  | word : Oria.Command.Word → BlockProperty
  /-- Static or runtime integer property value. -/
  | number : Scalar → BlockProperty

/-- Encode a property value without introducing runtime text computation. -/
@[expose] public def BlockProperty.fragment : BlockProperty → Oria.Command.Fragment EncodedVal
  | .word w => (encode w).fragment
  | .number n => (encode n).fragment

/-- Shared block description, parameterized by its head grammar. -/
public structure BlockDesc (a : Type) where
  /-- Concrete block ID or predicate ID/tag. -/
  id : a
  /-- Property constraints or assignments. Duplicate keys are rejected by Minecraft. -/
  properties : List (Oria.Command.Word × BlockProperty) := []
  /-- Optional block-entity NBT, including dynamic fragments or a runtime snapshot. -/
  data : Option Compound := none

/-- A concrete block state to place. -/
public abbrev BlockState := BlockDesc ResourceId

/-- A block or tag predicate for filtering native block operations. -/
public abbrev BlockPredicate := BlockDesc ResourceOrTag

/-- Encode the common suffix while preserving the head's grammar and all fragment requirements. -/
@[expose] public def BlockDesc.fragment {a : Type} [Oria.Command.ArgCodec a]
    (block : BlockDesc a) : Oria.Command.Fragment EncodedVal :=
  let props : Fragment EncodedVal := match block.properties with
    | [] => .empty
    | xs =>
        let fields : List (Fragment EncodedVal) := xs.map fun (key, val) =>
          (encode key).fragment.append ((Fragment.token "=").append (BlockProperty.fragment val))
        (Fragment.token "[").append
          ((fields.intersperse (Fragment.token ",")).foldl Fragment.append Fragment.empty |>.append (Fragment.token "]"))
  (encode block.id).fragment.append props |>.append
    ((block.data.map (fun d => (encode d).fragment)).getD .empty)

public instance : Oria.Command.ArgCodec BlockState where
  key := ⟨`minecraft.argument.block_state⟩
  encode := BlockDesc.fragment

public instance : Oria.Command.ArgCodec BlockPredicate where
  key := ⟨`minecraft.argument.block_predicate⟩
  encode := BlockDesc.fragment

/-- Dependencies of the head, property values, and NBT suffix. -/
@[expose] public def BlockDesc.requirements {a : Type} [Oria.Command.ArgCodec a]
    (block : BlockDesc a) : ReqRow := block.fragment.requirements

@[simp] public theorem BlockState.encode_requirements (block : BlockState) :
    (encode block).requirements = block.requirements := rfl

@[simp] public theorem BlockPredicate.encode_requirements (block : BlockPredicate) :
    (encode block).requirements = block.requirements := rfl

/-- Inclusive region between two block positions; corner order is interpreted natively. -/
public structure BlockBox where
  /-- First corner. -/
  start : BlockPos
  /-- Opposite corner. -/
  finish : BlockPos

public instance : Oria.Command.ArgCodec BlockBox where
  key := ⟨`minecraft.argument.block_box⟩
  encode b := .spaced [(encode b.start).fragment, (encode b.finish).fragment]

/-- Corner-coordinate requirements. -/
@[expose] public def BlockBox.requirements (b : BlockBox) : ReqRow := (encode b).requirements

/-- Native setblock behavior. -/
public inductive SetBlockMode where
  /-- Replace with normal block updates. -/
  | replace
  /-- Destroy the existing block with native drops. -/
  | destroy
  /-- Place only in air. -/
  | keep
  /-- Place without neighbor and shape updates. -/
  | strict

public instance : Oria.Command.ArgCodec SetBlockMode where
  key := ⟨`minecraft.argument.setblock_mode⟩
  encode m := .token (match m with
    | .replace => "replace" | .destroy => "destroy" | .keep => "keep" | .strict => "strict")

@[simp] public theorem SetBlockMode.encode_requirements (m : SetBlockMode) :
    (encode m).requirements = Req.none := rfl

/-- Fill behavior applied after an optional replacement filter. -/
public inductive FillStyle where
  /-- Replace with ordinary updates. -/
  | normal
  /-- Destroy old blocks before placement. -/
  | destroy
  /-- Place the boundary and clear the interior. -/
  | hollow
  /-- Place only the boundary. -/
  | outline
  /-- Place without neighbor and shape updates. -/
  | strict

/-- Encode a fill placement style. -/
@[expose] public def FillStyle.fragment : FillStyle → Oria.Command.Fragment EncodedVal
  | .normal => .empty
  | .destroy => .token "destroy"
  | .hollow => .token "hollow"
  | .outline => .token "outline"
  | .strict => .token "strict"

/-- Legal combinations of fill filtering and placement behavior. -/
public inductive FillMode where
  /-- Place only in air. -/
  | keep
  /-- Optional block filter followed by a placement style. -/
  | replace (filter : Option BlockPredicate := none) (style : FillStyle := .normal)

public instance : Oria.Command.ArgCodec FillMode where
  key := ⟨`minecraft.argument.fill_mode⟩
  encode
    | .keep => .token "keep"
    | .replace filter style => .spaced
        (filter.toList.flatMap (fun p => [.token "replace", (encode p).fragment]) ++ [FillStyle.fragment style])

/-- Context carried by any dynamic predicate values. -/
@[expose] public def FillMode.requirements (m : FillMode) : ReqRow := (encode m).requirements

/-- Block selection for clone. -/
public inductive CloneFilter where
  /-- Copy every source block. -/
  | all
  /-- Skip source air. -/
  | masked
  /-- Copy source blocks satisfying the predicate. -/
  | filtered : BlockPredicate → CloneFilter

/-- Encode the source-block selection. -/
@[expose] public def CloneFilter.fragment : CloneFilter → Oria.Command.Fragment EncodedVal
  | .all => .token "replace"
  | .masked => .token "masked"
  | .filtered p => .spaced [.token "filtered", (encode p).fragment]

/-- Native source/destination overlap behavior. -/
public inductive CloneMode where
  /-- Reject overlapping source and destination. -/
  | normal
  /-- Permit overlap. -/
  | force
  /-- Move the selected source blocks. -/
  | move

/-- Encode native overlap and movement behavior. -/
@[expose] public def CloneMode.fragment : CloneMode → Oria.Command.Fragment EncodedVal
  | .normal => .token "normal"
  | .force => .token "force"
  | .move => .token "move"

/-- Clone request, including optional dimensions and native mode ordering. -/
public structure CloneSpec where
  /-- Source region. -/
  source : BlockBox
  /-- Destination's lowest corner. -/
  destination : BlockPos
  /-- Source dimension; none uses the command dimension. -/
  sourceDimension : Option ResourceId := none
  /-- Destination dimension; none uses the command dimension. -/
  targetDimension : Option ResourceId := none
  /-- Suppress neighbor and shape updates. -/
  strict : Bool := false
  /-- Select source blocks. -/
  filter : CloneFilter := .all
  /-- Overlap/movement behavior. -/
  mode : CloneMode := .normal

public instance : Oria.Command.ArgCodec CloneSpec where
  key := ⟨`minecraft.argument.clone_spec⟩
  encode c := .spaced
    (c.sourceDimension.toList.flatMap (fun d => [.token "from", (encode d).fragment]) ++
      [(encode c.source).fragment] ++
      c.targetDimension.toList.flatMap (fun d => [.token "to", (encode d).fragment]) ++
      [(encode c.destination).fragment] ++
      (if c.strict then [.token "strict"] else []) ++
      [CloneFilter.fragment c.filter, CloneMode.fragment c.mode])

/-- Coordinate and predicate requirements; the command also reads its dimension's game rules. -/
@[expose] public def CloneSpec.requirements (c : CloneSpec) : ReqRow := (encode c).requirements

end Oria.Std.Command.Arg
