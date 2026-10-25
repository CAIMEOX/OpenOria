module

public import Oria.Std.Command.Arg
public import Oria.Std.Command.Arg.Management

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Scoreboard criteria

Criteria describe how Minecraft updates an objective. The common dummy and trigger criteria
have dedicated constructors. Other native criteria use a validated command token; Minecraft
checks the criterion name when parsing the command.
-/

namespace Oria.Std.Command.Arg

/-- An objective's native update criterion, fixed at construction time. -/
public inductive Criterion where
  /-- Scores are maintained explicitly by commands. -/
  | dummy
  /-- Players can submit an input after their score has been enabled. -/
  | trigger
  /-- Another native criterion, such as health or a namespaced statistic. -/
  | named : Oria.Command.SyntaxToken → Criterion

public instance : Oria.Command.ArgCodec Criterion where
  key := ⟨`minecraft.argument.objective_criteria⟩
  encode
    | .dummy => .token "dummy"
    | .trigger => .token "trigger"
    | .named name => .token name

@[simp] public theorem Criterion.encode_requirements (criterion : Criterion) :
    (Oria.Command.encode criterion).requirements = Req.none := by
  cases criterion <;> rfl

/-- A selection of scores in one objective, for native bulk operations. -/
public structure Scores where
  /-- Named, selected, or all tracked holders. -/
  holders : Holders
  /-- Existing native objective. -/
  objective : Oria.Command.Objective

public instance : Oria.Command.ArgCodec Scores where
  key := ⟨`minecraft.argument.scores⟩
  encode s := .spaced
    [(Oria.Command.encode s.holders).fragment, (Oria.Command.encode s.objective).fragment]

/-- Context used by the holder selection. -/
@[expose] public def Scores.requirements (s : Scores) : ReqRow := s.holders.requirements

@[simp] public theorem Scores.encode_requirements (s : Scores) :
    (Oria.Command.encode s).requirements = s.requirements := by
  simp [Oria.Command.encode, Oria.Command.ArgCodec.encode, Oria.Command.EncodedArg.requirements,
    Oria.Command.Fragment.spaced, Oria.Command.Fragment.append, Oria.Command.Fragment.token,
    Oria.Command.Fragment.space, Scores.requirements, Holders.requirements, Req.none]

end Oria.Std.Command.Arg
