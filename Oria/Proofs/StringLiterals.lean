module

import Oria
import Oria.Datapack
import Oria.Proofs.Fixtures.StringLiteral
meta import Oria

namespace Oria.Proofs.StringLiterals

open Oria.Datapack Oria.Std.Command.Arg

private def token : Command.SyntaxToken := "execute"
private def objective : Command.Objective := "points"
private def resource : ResourceId := "demo:loot/stone"
private def holder : ScoreHolderName := "#total"
private def resourceNamespace : ResourceNamespace := "demo"
private def path : ResourcePath := "__oria/helper"
private def publicPath : PublicFunctionPath := "game/start"

example : token.text = "execute" := rfl
example : objective = Command.Objective.ofString "points" := rfl
example : resource.text = "demo:loot/stone" := rfl
example : holder = ScoreHolderName.ofString "#total" := rfl
example : resourceNamespace.render = "demo" := rfl
example : path.render = "__oria/helper" := rfl
example : publicPath.render = "game/start" := rfl

private def settings : Settings := { ns := "game", objective := some "game.vm" }
example : settings.ns.render = "game" := rfl

private abbrev ResourceAlias := ResourceId
private def aliasValue : ResourceAlias := "demo:item"
private def expandedNamespace : {s : String // ResourceNamespace.Valid s} := "demo"
example : aliasValue.text = "demo:item" := rfl
example : expandedNamespace.val = "demo" := rfl

private def resources : List ResourceId := ["demo:one", "demo:two"]
example : resources.length = 2 := rfl
private def contextual : ResourceId := id "demo:contextual"
example : contextual.text = "demo:contextual" := rfl

private def ordinary := "ordinary text with spaces"
example : String := ordinary
example : String := id "demo:still_a_string"
#guard "abc".contains "b"
#guard ("a-b".splitOn "-").length == 2
private def stringPattern (s : String) : Bool := s.contains "needle"
#guard stringPattern "a needle"
run_cmd do
  let s ← pure ("needle" : String)
  if s.contains "needle" then pure () else throwError "missing string pattern"
private def inferredList := ["demo:a", "demo:b"]
example : List String := inferredList

example : Prog (Oria.Std.Scoreboard.readGrade .self) Int32 :=
  Oria.Std.Scoreboard.get .self "points"
example : ScoreHolder := .named "#total"

/-- error: invalid string literal -/
#guard_msgs(error, substring := true) in
example : Command.SyntaxToken := "two words"

/-- error: invalid string literal -/
#guard_msgs(error, substring := true) in
example : ResourceId := "demo:Uppercase"

/-- error: invalid string literal -/
#guard_msgs(error, substring := true) in
example : PublicFunctionPath := "__oria/private"

/-- error: invalid string literal -/
#guard_msgs(error, substring := true) in
example : ScoreHolderName := "@s"

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example (s : String) : ResourceId := s

example (s : String) : Except ResourceId.Error ResourceId := ResourceId.parse s
example (s : String) (h : ResourceId.Valid s) : ResourceId := ResourceId.ofString s h

private def downstream : Fixtures.StringLiteral.Name := "custom"
example : downstream = Fixtures.StringLiteral.Name.ofString "custom" := rfl

/-- error: invalid string literal -/
#guard_msgs(error, substring := true) in
example : Fixtures.StringLiteral.Name := ""

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example : Target := "@s"

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example : Command.Inline := "say hello"

namespace Registration

public structure Label where
  text : String

public def implicitInput {s : String} : Label := ⟨s⟩

/-- error: string_literal constructors must accept an explicit String first -/
#guard_msgs(error, substring := true) in
attribute [string_literal implicitInput] Label

public def requiredFlag (s : String) (_ : Bool) : Label := ⟨s⟩

/-- error: string_literal constructors may only require automatic proofs -/
#guard_msgs(error, substring := true) in
attribute [string_literal requiredFlag] Label

public def wrongResult (s : String) : String := s

/-- error: string_literal constructor must return -/
#guard_msgs(error, substring := true) in
attribute [string_literal wrongResult] Label

public structure Universal.{u} : Type (u + 1) where
  text : String

public def Universal.ofString.{u} (s : String) : Universal.{u} := ⟨s⟩

/-- error: string_literal targets must be monomorphic -/
#guard_msgs(error, substring := true) in
attribute [string_literal Universal.ofString] Universal

end Registration

section

abbrev AnotherName := Fixtures.StringLiteral.Name
attribute [local string_literal Fixtures.StringLiteral.Name.ofString] AnotherName

/-- error: ambiguous string literal -/
#guard_msgs(error, substring := true) in
example : AnotherName := "custom"

end

example : Fixtures.StringLiteral.Name := "custom"

end Oria.Proofs.StringLiterals
