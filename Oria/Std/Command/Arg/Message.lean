module

public import Oria.Std.Command.Arg
public import Init.Data.String.Lemmas.Pattern.Find.String
public meta import Lean.Elab.Tactic.Cbv

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Native chat messages

Message builds the greedy message argument used by say, msg, teammsg, and me.
Plain text, selectors, and runtime integers retain their own context requirements.
Join inserts spaces between complete fragments so a suffix cannot extend a selector's grammar.
Native text uses Minecraft's message parser and conservatively requires all context.
-/

namespace Oria.Std.Command.Arg

namespace Message

/-- Nonblank command-line text containing no selector marker or macro substitution. -/
@[expose] public def Plain (s : String) : Prop :=
  Oria.Command.Inline.Valid s ∧ (∃ c ∈ s.toList, c ≠ ' ') ∧ ¬s.contains "@"

public instance (s : String) : Decidable (Plain s) := by unfold Plain; infer_instance

end Message

/-- A host-built native message with typed numeric holes and a context summary. -/
public structure Message where
  private mk ::
  private fragment : Oria.Command.Fragment EncodedVal
  /-- Implicit inputs used when Minecraft resolves the message. -/
  requirements : ReqRow

namespace Message

/-- Checked plain text. Spaces are preserved; selector expansion uses selector or native. -/
public def ofString (s : String)
    (h : Plain s := by
      cbv
      simp +decide) : Message :=
  ⟨.inline (.ofString s h.1), Req.none⟩

/-- Validate plain text computed during construction. -/
public def parse (s : String) : Except Diagnostic Message :=
  if h : Plain s then pure (ofString s h) else throw (.invalidCommandText s)

/-- Native message text, including selector syntax. Minecraft parses and expands it.
This form retains the conservative full-context requirement. -/
public def native (s : String)
    (h : Oria.Command.Inline.Valid s := by
      cbv
      simp +decide) : Message :=
  ⟨.inline (.ofString s h), Req.all⟩

/-- Expand a structured selector to the selected entities' display names. -/
public def selector (s : Oria.Command.Selector) : Message := ⟨s.fragment, s.requirements⟩

/-- Insert a static or runtime integer in decimal spelling. -/
public def number (n : Scalar) : Message := ⟨(Oria.Command.encode n).fragment, Req.none⟩

/-- Join nonempty message fragments with spaces. The first fragment is required.
The separation keeps each selector complete before the following fragment begins. -/
public def join (first : Message) (rest : List Message) : Message :=
  ⟨.spaced ((first :: rest).map (·.fragment)),
    ((first :: rest).map (·.requirements)).foldr (· ||| ·) Req.none⟩

@[simp] public theorem ofString_requirements (s : String) (h : Plain s) :
    (ofString s h).requirements = Req.none := private_decl% (by rfl)
@[simp] public theorem native_requirements (s : String) (h : Oria.Command.Inline.Valid s) :
    (native s h).requirements = Req.all := private_decl% (by rfl)
@[simp] public theorem selector_requirements (s : Oria.Command.Selector) :
    (selector s).requirements = s.requirements := private_decl% (by rfl)
@[simp] public theorem number_requirements (n : Scalar) :
    (number n).requirements = Req.none := private_decl% (by rfl)
@[simp] public theorem join_requirements (first : Message) (rest : List Message) :
    (join first rest).requirements =
      first.requirements ||| (rest.map (·.requirements)).foldr (· ||| ·) Req.none :=
  private_decl% (by rfl)

end Message

attribute [string_literal Message.ofString] Message

public instance : Oria.Command.ArgCodec Message where
  key := ⟨`minecraft.argument.message⟩
  encode m := private_decl% { m.fragment with requirements := m.requirements }

@[simp] public theorem Message.encode_requirements (m : Message) :
    (Oria.Command.encode m).requirements = m.requirements := private_decl% (by rfl)
@[simp] public theorem Message.encode_fragment_requirements (m : Message) :
    (Oria.Command.encode m).fragment.requirements = m.requirements := private_decl% (by rfl)

end Oria.Std.Command.Arg
