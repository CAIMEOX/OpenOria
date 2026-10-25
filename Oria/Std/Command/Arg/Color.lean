module

public import Oria.Std.Command.Arg

set_option doc.verso true
set_option linter.missingDocs true

namespace Oria.Std.Command.Arg

namespace HexColor

/-- Three or six ASCII hexadecimal digits, without a prefix. -/
@[expose] public def Valid (s : String) : Prop :=
  (s.length = 3 ∨ s.length = 6) ∧ ∀ c ∈ s.toList, c.isHexDigit

public instance (s : String) : Decidable (Valid s) := by unfold Valid; infer_instance

end HexColor

/-- Checked host RGB spelling for native hexadecimal color arguments. -/
public structure HexColor where
  private mk ::
  /-- Original spelling, including its three- or six-digit form. -/
  text : String
  /-- Native lexical invariant. -/
  valid : HexColor.Valid text
  deriving BEq, DecidableEq, Repr

namespace HexColor

/-- Check a literal, or supply an existing proof for computed text. -/
public def ofString (text : String) (valid : Valid text := by decide) : HexColor :=
  ⟨text, valid⟩

/-- Validate a color computed during construction. -/
public def parse (text : String) : Except Diagnostic HexColor :=
  if h : Valid text then pure ⟨text, h⟩ else throw (.invalidCommandText text)

end HexColor

attribute [string_literal HexColor.ofString] HexColor

public instance : Oria.Command.ArgCodec HexColor where
  key := ⟨`minecraft.argument.hex_color⟩
  encode c := ⟨[.literal (.unquoted c.text)], Req.none⟩

end Oria.Std.Command.Arg
