module

public import Init
public meta import Oria.Data.StringLiteral

namespace Oria

namespace ResourceId

public inductive Error where
  | invalidResourceId (text : String)
  deriving BEq, DecidableEq, Repr

@[expose] public def NamespaceCharacter (character : Char) : Prop :=
  ('a' ≤ character ∧ character ≤ 'z') ∨
    ('0' ≤ character ∧ character ≤ '9') ∨
      character = '_' ∨ character = '-' ∨ character = '.'

public instance (character : Char) : Decidable (NamespaceCharacter character) := by
  unfold NamespaceCharacter
  infer_instance

@[expose] public def PathCharacter (character : Char) : Prop :=
  NamespaceCharacter character ∨ character = '/'

public instance (character : Char) : Decidable (PathCharacter character) := by
  unfold PathCharacter
  infer_instance

@[expose] public def NamespaceTail : List Char → Prop
  | [] => False
  | character :: rest =>
      if character = ':' then
        rest ≠ [] ∧ ∀ pathCharacter ∈ rest, PathCharacter pathCharacter
      else
        NamespaceCharacter character ∧ NamespaceTail rest

public instance instDecidableNamespaceTail :
    (characters : List Char) → Decidable (NamespaceTail characters)
  | [] => by
      simp only [NamespaceTail]
      infer_instance
  | character :: rest => by
      if colon : character = ':' then
        simp only [NamespaceTail, colon, if_true]
        infer_instance
      else
        simp only [NamespaceTail, colon, if_false]
        let _ : Decidable (NamespaceTail rest) := instDecidableNamespaceTail rest
        infer_instance

/-- The canonical, explicitly namespaced Minecraft resource-location grammar. -/
@[expose] public def Valid (text : String) : Prop :=
  match text.toList with
  | [] => False
  | character :: rest =>
      NamespaceCharacter character ∧ NamespaceTail rest

public instance (text : String) : Decidable (Valid text) := by
  unfold Valid
  generalize text.toList = characters
  cases characters with
  | nil => infer_instance
  | cons _ rest =>
      let _ : Decidable (NamespaceTail rest) := instDecidableNamespaceTail rest
      infer_instance

end ResourceId

public structure ResourceId where
  text : String
  valid : ResourceId.Valid text := by decide
  deriving BEq, DecidableEq, Hashable, Repr

namespace ResourceId

@[expose] public def ofString
    (text : String)
    (valid : Valid text := by decide) : ResourceId :=
  ⟨text, valid⟩

public def parse (text : String) : Except Error ResourceId :=
  if valid : Valid text then
    .ok ⟨text, valid⟩
  else
    .error (.invalidResourceId text)

end ResourceId

attribute [string_literal ResourceId.ofString] ResourceId

end Oria
