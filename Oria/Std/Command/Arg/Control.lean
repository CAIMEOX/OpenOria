module

public import Oria.Std.Command.Arg.Position
public import Oria.Std.Command.Arg.World
public import Oria.Std.Command.Arg.Nbt

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

namespace Oria.Std.Command.Arg
open Oria.Command (encode)

/-- Native attribute modifier operation. -/
public inductive AttributeOperation where
  /-- Add the amount. -/
  | add
  /-- Add a multiple of the value after flat additive modifiers. -/
  | multiplyBase
  /-- Multiply the running total by one plus the amount. -/
  | multiplyTotal

public instance : Oria.Command.ArgCodec AttributeOperation where
  key := ⟨`minecraft.argument.attribute_operation⟩
  encode op := .token (match op with
    | .add => "add_value" | .multiplyBase => "add_multiplied_base"
    | .multiplyTotal => "add_multiplied_total")

/-- Attribute query or update, with host or runtime numeric leaves. -/
public inductive AttributeAction where
  /-- Query the computed value, multiplied by the supplied scale. -/
  | get : Decimal → AttributeAction
  /-- Query the base value with a scale. -/
  | base : Decimal → AttributeAction
  /-- Assign the base value. -/
  | set : Decimal → AttributeAction
  /-- Restore the entity type's default base value. -/
  | reset
  /-- Add a persistent native attribute modifier. -/
  | add : ResourceId → Decimal → AttributeOperation → AttributeAction
  /-- Remove a modifier by its resource ID. -/
  | remove : ResourceId → AttributeAction
  /-- Query a modifier's amount with a scale. -/
  | modifier : ResourceId → Decimal → AttributeAction

public instance : Oria.Command.ArgCodec AttributeAction where
  key := ⟨`minecraft.argument.attribute_action⟩
  encode action :=
    let f : Oria.Command.Fragment EncodedVal := match action with
      | .get n => .spaced [.token "get", (encode n).fragment]
      | .base n => .spaced [.token "base", .token "get", (encode n).fragment]
      | .set n => .spaced [.token "base", .token "set", (encode n).fragment]
      | .reset => .spaced [.token "base", .token "reset"]
      | .add id n op => .spaced [.token "modifier", .token "add",
          (encode id).fragment, (encode n).fragment, (encode op).fragment]
      | .remove id => .spaced [.token "modifier", .token "remove", (encode id).fragment]
      | .modifier id n => .spaced [.token "modifier", .token "value", .token "get",
          (encode id).fragment, (encode n).fragment]
    ⟨f.segments, Req.none⟩

@[simp] public theorem AttributeAction.encode_requirements (a : AttributeAction) :
    (encode a).requirements = Req.none := rfl

/-- Forced-chunk management. Positions are block coordinates, not chunk indices. -/
public inductive ForceloadAction where
  /-- Add the inclusive chunk rectangle containing the coordinates. -/
  | add : ColumnPos → Option ColumnPos → ForceloadAction
  /-- Remove the corresponding rectangle. -/
  | remove : ColumnPos → Option ColumnPos → ForceloadAction
  /-- Clear all forced chunks in the dimension. -/
  | clear
  /-- Query whether one chunk is forced. -/
  | query : ColumnPos → ForceloadAction
  /-- Query the number of forced chunks. -/
  | list

public instance : Oria.Command.ArgCodec ForceloadAction where
  key := ⟨`minecraft.argument.forceload_action⟩
  encode
    | .add p q => .spaced ([.token "add", (encode p).fragment] ++
        q.toList.map (fun p => (encode p).fragment))
    | .remove p q => .spaced ([.token "remove", (encode p).fragment] ++
        q.toList.map (fun p => (encode p).fragment))
    | .clear => .spaced [.token "remove", .token "all"]
    | .query p => .spaced [.token "query", (encode p).fragment]
    | .list => .token "query"

/-- Requirements of the selected coordinates. -/
@[expose] public def ForceloadAction.requirements (a : ForceloadAction) : ReqRow :=
  (encode a).requirements

/-- Settings for native random placement on safe ground. -/
public structure SpreadSettings where
  /-- Minimum separation in blocks; must be nonnegative. -/
  distance : Decimal
  /-- Maximum range from the center; native minimum is one. -/
  range : Decimal
  /-- Optional upper search bound; the dimension's maximum is used otherwise. -/
  under : Option Scalar := none
  /-- Keep each native team together. -/
  respectTeams : Bool := false

public instance : Oria.Command.ArgCodec SpreadSettings where
  key := ⟨`minecraft.argument.spread_settings⟩
  encode s :=
    let f := Oria.Command.Fragment.spaced
      ([(encode s.distance).fragment, (encode s.range).fragment] ++
        s.under.toList.flatMap (fun y => [.token "under", (encode y).fragment]) ++
        [(encode s.respectTeams).fragment])
    ⟨f.segments, Req.none⟩

@[simp] public theorem SpreadSettings.encode_requirements (s : SpreadSettings) :
    (encode s).requirements = Req.none := rfl

/-- Hand used by entity animation and inventory-related command arguments. -/
public inductive Hand where
  /-- Main hand. -/
  | mainhand
  /-- Off hand. -/
  | offhand

public instance : Oria.Command.ArgCodec Hand where
  key := ⟨`minecraft.argument.hand⟩
  encode h := .token (match h with | .mainhand => "mainhand" | .offhand => "offhand")

/-- Swing animation understood by DP121. -/
public inductive SwingAnimation where
  /-- Suppress the animation. -/
  | none
  /-- Standard sweeping swing. -/
  | whack
  /-- Stabbing animation. -/
  | stab

public instance : Oria.Command.ArgCodec SwingAnimation where
  key := ⟨`minecraft.argument.swing_animation⟩
  encode a := .token (match a with | .none => "none" | .whack => "whack" | .stab => "stab")

/-- Native swing parameters; the duration must resolve to a positive tick count. -/
public structure SwingSettings where
  /-- Selected hand. -/
  hand : Hand := .mainhand
  /-- Selected animation. -/
  animation : SwingAnimation := .whack
  /-- Native animation duration. -/
  duration : Time := .ticks (.static 6)

public instance : Oria.Command.ArgCodec SwingSettings where
  key := ⟨`minecraft.argument.swing_settings⟩
  encode s :=
    let f := Oria.Command.Fragment.spaced
      [(encode s.hand).fragment, (encode s.animation).fragment, (encode s.duration).fragment]
    ⟨f.segments, Req.none⟩

@[simp] public theorem SwingSettings.encode_requirements (s : SwingSettings) :
    (encode s).requirements = Req.none := rfl

/-- Registry particle plus native codec options. Options reuse static, mixed-field, or runtime NBT. -/
public structure ParticleSpec where
  /-- Registered particle type. -/
  id : ResourceId
  /-- Options parsed by that particle's native codec. -/
  options : Compound := .value (nbt% {})

public instance : Oria.Command.ArgCodec ParticleSpec where
  key := ⟨`minecraft.argument.particle⟩
  encode p := (encode p.id).fragment.append (encode p.options).fragment

/-- Context required by the options fragment. -/
@[expose] public def ParticleSpec.requirements (p : ParticleSpec) : ReqRow :=
  (encode p).requirements

/-- Particle distribution and viewer selection. Count zero selects native directional behavior. -/
public structure ParticleSettings where
  /-- Origin, defaulting to the execution position. -/
  position : Vec3 := .world (.relative (.static 0)) (.relative (.static 0)) (.relative (.static 0))
  /-- Native delta vector; absolute components are literal spreads without block centering. -/
  delta : Vec3 := .world (.absolute (.static 0)) (.absolute (.static 0)) (.absolute (.static 0))
  /-- Nonnegative speed. -/
  speed : Decimal := .static 0
  /-- Nonnegative particle count. -/
  count : Scalar := .static 1
  /-- Use native force delivery distance. -/
  force : Bool := false
  /-- Potential packet recipients. -/
  viewers : Players := .all

public instance : Oria.Command.ArgCodec ParticleSettings where
  key := ⟨`minecraft.argument.particle_settings⟩
  encode s := .spaced [(encode s.position).fragment, (encode s.delta).fragment,
    (encode s.speed).fragment, (encode s.count).fragment,
    .token (if s.force then "force" else "normal"), (encode s.viewers).fragment]

/-- Coordinate and viewer requirements. -/
@[expose] public def ParticleSettings.requirements (s : ParticleSettings) : ReqRow :=
  (encode s).requirements

end Oria.Std.Command.Arg
