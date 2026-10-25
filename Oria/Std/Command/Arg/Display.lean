module

public import Oria.Std.Command.Arg.Management
public import Oria.Std.Command.Arg.Nbt

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Scoreboard display arguments

Display slots, objective properties, and number formats are host descriptions. Text and
NBT leaves reuse the standard encoders, including dynamic integer text. Format reset emits
the native omitted argument and restores the receiving objective or score's default.
-/

namespace Oria.Std.Command.Arg
open Oria.Command (encode)

/-- Native scoreboard display location. -/
public inductive DisplaySlot where
  /-- Player-list scores. -/
  | list
  /-- Global sidebar. -/
  | sidebar
  /-- Scores below player names. -/
  | belowName
  /-- Sidebar for viewers of a given team color. -/
  | sidebarTeam : TeamColor → DisplaySlot

public instance : Oria.Command.ArgCodec DisplaySlot where
  key := ⟨`minecraft.argument.display_slot⟩
  encode slot :=
    let f : Oria.Command.Fragment EncodedVal := match slot with
      | .list => .token "list"
      | .sidebar => .token "sidebar"
      | .belowName => .token "below_name"
      | .sidebarTeam color => .prepend "sidebar.team." (encode color).fragment
    ⟨f.segments, Req.none⟩

@[simp] public theorem DisplaySlot.encode_requirements (s : DisplaySlot) :
    (encode s).requirements = Req.none := rfl

/-- Native numeric rendering for an objective. -/
public inductive ScoreRender where
  /-- Decimal integer. -/
  | integer
  /-- Heart icons. -/
  | hearts

public instance : Oria.Command.ArgCodec ScoreRender where
  key := ⟨`minecraft.argument.score_render⟩
  encode r := .token (match r with | .integer => "integer" | .hearts => "hearts")

/-- Number format shared by objectives and individual score overrides. -/
public inductive ScoreFormat where
  /-- Clear the explicit format and use native inheritance/defaults. -/
  | reset
  /-- Hide the numeric value. -/
  | blank
  /-- Display a fixed text component. -/
  | fixed : TextComponent → ScoreFormat
  /-- Apply a native NBT text style. -/
  | styled : Compound → ScoreFormat

public instance : Oria.Command.ArgCodec ScoreFormat where
  key := ⟨`minecraft.argument.score_format⟩
  encode
    | .reset => .empty
    | .blank => .token "blank"
    | .fixed t => .spaced [.token "fixed", (encode t).fragment]
    | .styled s => .spaced [.token "styled", (encode s).fragment]

/-- Requirements retained by text and style arguments. -/
@[expose] public def ScoreFormat.requirements (f : ScoreFormat) : ReqRow := (encode f).requirements

/-- Editable objective presentation. -/
public inductive ObjectiveProperty where
  /-- Display name. -/
  | displayName : TextComponent → ObjectiveProperty
  /-- Integer or heart rendering. -/
  | renderType : ScoreRender → ObjectiveProperty
  /-- Update score display names automatically. -/
  | autoUpdate : Bool → ObjectiveProperty
  /-- Objective-wide number format. -/
  | numberFormat : ScoreFormat → ObjectiveProperty

public instance : Oria.Command.ArgCodec ObjectiveProperty where
  key := ⟨`minecraft.argument.objective_property⟩
  encode
    | .displayName t => .spaced [.token "displayname", (encode t).fragment]
    | .renderType r => .spaced [.token "rendertype", (encode r).fragment]
    | .autoUpdate b => .spaced [.token "displayautoupdate", (encode b).fragment]
    | .numberFormat f => .spaced [.token "numberformat", (encode f).fragment]

/-- Context requirements of the selected property. -/
@[expose] public def ObjectiveProperty.requirements (p : ObjectiveProperty) : ReqRow :=
  (encode p).requirements

end Oria.Std.Command.Arg
