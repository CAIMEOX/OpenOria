module

public import Oria.Command.Syntax
public import Oria.Datapack.ResourceId

namespace Oria.Command

namespace Word

/-- A nonempty Brigadier unquoted word. -/
@[expose] public def Valid (text : String) : Prop := text ≠ "" ∧ Unquoted.Valid text

public instance (text : String) : Decidable (Valid text) := by unfold Valid; infer_instance

end Word

/-- A checked native word for names such as entity tags. -/
public structure Word where
  private mk ::
  /-- Nonempty unquoted text. -/
  text : String
  /-- Membership in the native word language. -/
  valid : Word.Valid text
  deriving BEq, DecidableEq, Repr

namespace Word

/-- Check a literal word, or supply an existing validity proof. -/
public def ofString (text : String) (valid : Valid text := by decide) : Word := ⟨text, valid⟩

/-- Validate a word computed during construction. -/
public def parse (text : String) : Except Diagnostic Word :=
  if h : Valid text then pure ⟨text, h⟩ else throw (.invalidCommandText text)

end Word

attribute [string_literal Word.ofString] Word

private theorem resourceCharacter (c : Char) (h : ResourceId.PathCharacter c ∨ c = ':') :
    32 ≤ c.toNat ∧ c.toNat ≠ 127 ∧ ¬c.isWhitespace ∧ c ≠ '$' ∧ c ≠ '"' ∧ c ≠ '\\' := by
  rcases h with ((h | h | rfl | rfl | rfl) | rfl) | rfl
  all_goals simp_all [Char.isWhitespace, Char.le_def, Char.toNat, UInt32.le_iff_toNat_le, -Char.toNat_val]
  all_goals repeat' apply And.intro
  all_goals try omega
  all_goals intro eq; subst c; simp_all

private theorem resourceTail (chars : List Char) (valid : ResourceId.NamespaceTail chars) :
    ∀ c ∈ chars, ResourceId.PathCharacter c ∨ c = ':' := by
  induction chars with
  | nil => simp
  | cons head rest ih =>
    simp only [ResourceId.NamespaceTail] at valid
    split at valid
    · rename_i colon
      intro c member
      rcases List.mem_cons.mp member with rfl | member
      · exact .inr colon
      · exact .inl (valid.2 c member)
    · intro c member
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl (.inl valid.1)
      · exact ih valid.2 c member

private theorem resourceValid (id : ResourceId) : SyntaxToken.Valid id.text := by
  have valid := id.valid
  unfold ResourceId.Valid at valid
  generalize hc : id.text.toList = chars at valid
  cases chars with
  | nil => contradiction
  | cons head rest =>
    refine ⟨?_, ?_⟩
    · intro empty
      simp [empty] at hc
    · intro c member
      rw [hc] at member
      apply resourceCharacter
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl (.inl valid.1)
      · exact resourceTail rest valid.2 c member

/-- Resource locations preserve the lexical command-token invariant. -/
public def SyntaxToken.ofResourceId (id : ResourceId) : SyntaxToken :=
  ⟨id.text, resourceValid id⟩

/-- A scoreboard objective name shared by source commands and physical commands. -/
public structure Objective where
  private mk ::
  token : SyntaxToken
  deriving BEq, DecidableEq, Repr

namespace Objective

@[expose] public def ofToken (token : SyntaxToken) : Objective :=
  private_decl% ⟨token⟩

public def ofString (text : String) (valid : SyntaxToken.Valid text := by decide) : Objective :=
  ofToken (.ofString text valid)

public def parse (text : String) : Except Diagnostic Objective :=
  ofToken <$> SyntaxToken.parse text

end Objective

attribute [string_literal Objective.ofString] Objective

/-- Minecraft scoreboard arithmetic and assignment operations. -/
public inductive ScoreOp where
  | assign
  | add
  | subtract
  | multiply
  | divide
  | modulo
  | minimum
  | maximum
  | swap
  deriving BEq, DecidableEq, Repr

namespace ScoreOp

@[expose] public def token : ScoreOp → SyntaxToken
  | .assign => "="
  | .add => "+="
  | .subtract => "-="
  | .multiply => "*="
  | .divide => "/="
  | .modulo => "%="
  | .minimum => "<"
  | .maximum => ">"
  | .swap => "><"

end ScoreOp

/-- Native player game mode, shared by commands and selector filters. -/
public inductive GameMode where
  | survival | creative | adventure | spectator
  deriving BEq, DecidableEq, Repr

@[expose] public def GameMode.token : GameMode → SyntaxToken
  | .survival => "survival"
  | .creative => "creative"
  | .adventure => "adventure"
  | .spectator => "spectator"

/-- One registry entry or a registry tag. -/
public inductive ResourceOrTag where
  | id : ResourceId → ResourceOrTag
  | tag : ResourceId → ResourceOrTag

@[expose] public def ResourceOrTag.fragment {v : ObjTy → Type} : ResourceOrTag → Fragment v
  | .id r => .token (.ofResourceId r)
  | .tag r => .prepend "#" (.token (.ofResourceId r))

end Oria.Command
