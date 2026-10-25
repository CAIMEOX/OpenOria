module

public import Oria.Std.Command.Arg.Text

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

namespace Oria.Std.Command.Arg

/-- Boss-bar colors. -/
public inductive BarColor where
  /-- pink. -/
  | pink
  /-- blue. -/
  | blue
  /-- red. -/
  | red
  /-- green. -/
  | green
  /-- yellow. -/
  | yellow
  /-- purple. -/
  | purple
  /-- white. -/
  | white
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec BarColor where
  key := ⟨`minecraft.argument.barcolor⟩
  encode value := .token (match value with
    | .pink => "pink"
    | .blue => "blue"
    | .red => "red"
    | .green => "green"
    | .yellow => "yellow"
    | .purple => "purple"
    | .white => "white")

@[simp] public theorem BarColor.encode_requirements (value : BarColor) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem BarColor.encode_fragment_requirements (value : BarColor) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

/-- Boss-bar segment style. -/
public inductive BarStyle where
  /-- progress. -/
  | progress
  /-- notched 6. -/
  | notched_6
  /-- notched 10. -/
  | notched_10
  /-- notched 12. -/
  | notched_12
  /-- notched 20. -/
  | notched_20
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec BarStyle where
  key := ⟨`minecraft.argument.barstyle⟩
  encode value := .token (match value with
    | .progress => "progress"
    | .notched_6 => "notched_6"
    | .notched_10 => "notched_10"
    | .notched_12 => "notched_12"
    | .notched_20 => "notched_20")

@[simp] public theorem BarStyle.encode_requirements (value : BarStyle) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem BarStyle.encode_fragment_requirements (value : BarStyle) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

/-- Queryable boss-bar fields. -/
public inductive BarField where
  /-- value. -/
  | value
  /-- max. -/
  | max
  /-- visible. -/
  | visible
  /-- players. -/
  | players
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec BarField where
  key := ⟨`minecraft.argument.barfield⟩
  encode v := .token (match v with
    | .value => "value"
    | .max => "max"
    | .visible => "visible"
    | .players => "players")

@[simp] public theorem BarField.encode_requirements (v : BarField) :
    (Oria.Command.encode v).requirements = Req.none := rfl

@[simp] public theorem BarField.encode_fragment_requirements (v : BarField) :
    (Oria.Command.encode v).fragment.requirements = Req.none := rfl

/-- The native named team colors. -/
public inductive TeamColor where
  /-- black. -/
  | black
  /-- dark blue. -/
  | dark_blue
  /-- dark green. -/
  | dark_green
  /-- dark aqua. -/
  | dark_aqua
  /-- dark red. -/
  | dark_red
  /-- dark purple. -/
  | dark_purple
  /-- gold. -/
  | gold
  /-- gray. -/
  | gray
  /-- dark gray. -/
  | dark_gray
  /-- blue. -/
  | blue
  /-- green. -/
  | green
  /-- aqua. -/
  | aqua
  /-- red. -/
  | red
  /-- light purple. -/
  | light_purple
  /-- yellow. -/
  | yellow
  /-- white. -/
  | white
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec TeamColor where
  key := ⟨`minecraft.argument.teamcolor⟩
  encode value := .token (match value with
    | .black => "black"
    | .dark_blue => "dark_blue"
    | .dark_green => "dark_green"
    | .dark_aqua => "dark_aqua"
    | .dark_red => "dark_red"
    | .dark_purple => "dark_purple"
    | .gold => "gold"
    | .gray => "gray"
    | .dark_gray => "dark_gray"
    | .blue => "blue"
    | .green => "green"
    | .aqua => "aqua"
    | .red => "red"
    | .light_purple => "light_purple"
    | .yellow => "yellow"
    | .white => "white")

@[simp] public theorem TeamColor.encode_requirements (value : TeamColor) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem TeamColor.encode_fragment_requirements (value : TeamColor) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

/-- Team-dependent visibility. -/
public inductive TeamVisibility where
  /-- always. -/
  | always
  /-- never. -/
  | never
  /-- hideForOtherTeams. -/
  | hideForOtherTeams
  /-- hideForOwnTeam. -/
  | hideForOwnTeam
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec TeamVisibility where
  key := ⟨`minecraft.argument.teamvisibility⟩
  encode value := .token (match value with
    | .always => "always"
    | .never => "never"
    | .hideForOtherTeams => "hideForOtherTeams"
    | .hideForOwnTeam => "hideForOwnTeam")

@[simp] public theorem TeamVisibility.encode_requirements (value : TeamVisibility) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem TeamVisibility.encode_fragment_requirements (value : TeamVisibility) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

/-- Team collision policy. -/
public inductive TeamCollision where
  /-- always. -/
  | always
  /-- never. -/
  | never
  /-- pushOtherTeams. -/
  | pushOtherTeams
  /-- pushOwnTeam. -/
  | pushOwnTeam
  deriving BEq, DecidableEq, Repr

public instance : Oria.Command.ArgCodec TeamCollision where
  key := ⟨`minecraft.argument.teamcollision⟩
  encode value := .token (match value with
    | .always => "always"
    | .never => "never"
    | .pushOtherTeams => "pushOtherTeams"
    | .pushOwnTeam => "pushOwnTeam")

@[simp] public theorem TeamCollision.encode_requirements (value : TeamCollision) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem TeamCollision.encode_fragment_requirements (value : TeamCollision) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl


/-- A score-holder selection, including fake names and the tracked-holder wildcard. -/
public inductive Holders where
  /-- One named holder or the executor. -/
  | one : ScoreHolder → Holders
  /-- Native entity selection. -/
  | entities : Target → Holders
  /-- All score holders tracked by the native scoreboard. -/
  | all

public instance : Oria.Command.ArgCodec Holders where
  key := ⟨`minecraft.argument.score_holders⟩
  encode
    | .one holder => (Oria.Command.encode holder).fragment
    | .entities targets => (Oria.Command.encode targets).fragment
    | .all => .token "*"

/-- Context requirements of the selected score holders. -/
@[expose] public def Holders.requirements (holders : Holders) : ReqRow :=
  (Oria.Command.encode holders).requirements

/-- A typed boss-bar update. Numeric bounds are checked by Minecraft. -/
public inductive BarProperty where
  /-- Display name. -/
  | name : TextComponent → BarProperty
  /-- Bar color. -/
  | color : BarColor → BarProperty
  /-- Segment style. -/
  | style : BarStyle → BarProperty
  /-- Current nonnegative value. -/
  | value : Scalar → BarProperty
  /-- Positive maximum. -/
  | max : Scalar → BarProperty
  /-- Visibility flag. -/
  | visible : Bool → BarProperty
  /-- Replace viewers; none clears them. -/
  | players : Option Players → BarProperty

public instance : Oria.Command.ArgCodec BarProperty where
  key := ⟨`minecraft.argument.bar_property⟩
  encode
    | .name x => .spaced [.token "name", (Oria.Command.encode x).fragment]
    | .color x => .spaced [.token "color", (Oria.Command.encode x).fragment]
    | .style x => .spaced [.token "style", (Oria.Command.encode x).fragment]
    | .value x => .spaced [.token "value", (Oria.Command.encode x).fragment]
    | .max x => .spaced [.token "max", (Oria.Command.encode x).fragment]
    | .visible x => .spaced [.token "visible", (Oria.Command.encode x).fragment]
    | .players x => .spaced (.token "players" :: x.toList.map (fun p => (Oria.Command.encode p).fragment))

/-- Requirements of text and viewer selection. -/
@[expose] public def BarProperty.requirements (property : BarProperty) : ReqRow :=
  (Oria.Command.encode property).requirements

/-- A typed native team-property update. -/
public inductive TeamProperty where
  /-- Team display name. -/
  | displayName : TextComponent → TeamProperty
  /-- Named color, or none to reset it. -/
  | color : Option TeamColor → TeamProperty
  /-- Friendly-fire policy. -/
  | friendlyFire : Bool → TeamProperty
  /-- See invisible teammates. -/
  | seeFriendlyInvisibles : Bool → TeamProperty
  /-- Nametag visibility. -/
  | nametagVisibility : TeamVisibility → TeamProperty
  /-- Death-message visibility. -/
  | deathMessageVisibility : TeamVisibility → TeamProperty
  /-- Collision policy. -/
  | collisionRule : TeamCollision → TeamProperty
  /-- Name prefix. -/
  | prefix : TextComponent → TeamProperty
  /-- Name suffix. -/
  | suffix : TextComponent → TeamProperty

public instance : Oria.Command.ArgCodec TeamProperty where
  key := ⟨`minecraft.argument.team_property⟩
  encode
    | .displayName x => .spaced [.token "displayName", (Oria.Command.encode x).fragment]
    | .color none => .spaced [.token "color", .token "reset"]
    | .color (some x) => .spaced [.token "color", (Oria.Command.encode x).fragment]
    | .friendlyFire x => .spaced [.token "friendlyFire", (Oria.Command.encode x).fragment]
    | .seeFriendlyInvisibles x => .spaced [.token "seeFriendlyInvisibles", (Oria.Command.encode x).fragment]
    | .nametagVisibility x => .spaced [.token "nametagVisibility", (Oria.Command.encode x).fragment]
    | .deathMessageVisibility x => .spaced [.token "deathMessageVisibility", (Oria.Command.encode x).fragment]
    | .collisionRule x => .spaced [.token "collisionRule", (Oria.Command.encode x).fragment]
    | .prefix x => .spaced [.token "prefix", (Oria.Command.encode x).fragment]
    | .suffix x => .spaced [.token "suffix", (Oria.Command.encode x).fragment]

/-- Requirements of text-bearing team properties. -/
@[expose] public def TeamProperty.requirements (property : TeamProperty) : ReqRow :=
  (Oria.Command.encode property).requirements

end Oria.Std.Command.Arg
