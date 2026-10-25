module

public import Oria.Nbt.Format
public import Oria.Diagnostic
public meta import Lean.Elab.Tactic.Decide

namespace Oria.Command

namespace Unquoted

/-- The alphabet accepted by Brigadier's unquoted-string reader. Empty strings are permitted
here because selector tag filters assign them a meaning. -/
@[expose] public def Valid (text : String) : Prop :=
  ∀ c ∈ text.toList, c ∈ "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_-.+".toList

public instance (text : String) : Decidable (Valid text) := by unfold Valid; infer_instance

end Unquoted

namespace Inline

/-- One physical command line with no function-macro substitutions. Grammar is checked by Minecraft. -/
@[expose] public def Valid (text : String) : Prop :=
  text ≠ "" ∧ (∀ c ∈ text.toList, 32 ≤ c.toNat ∧ c.toNat ≠ 127) ∧
    ¬text.contains "$("

public instance (text : String) : Decidable (Valid text) := by unfold Valid; infer_instance

end Inline

public structure Inline where
  text : String
  valid : Inline.Valid text := by native_decide
  deriving BEq, DecidableEq, Repr

namespace Inline

@[expose] public def ofString (text : String) (valid : Valid text := by native_decide) : Inline :=
  ⟨text, valid⟩

public def parse (text : String) : Except Diagnostic Inline :=
  if h : Valid text then .ok ⟨text, h⟩ else .error (.invalidCommandText text)

end Inline

/-- Static argument data carried intact until target formatting. -/
public inductive Literal where
  | nbt : Nbt.Any → Literal
  | inline : Inline → Literal
  /-- A Brigadier unquoted word. The empty word is meaningful in selector tag filters. -/
  | unquoted : String → Literal
  /-- A Brigadier quoted string, validated as one macro-independent physical line. -/
  | quoted : String → Literal
  | path : Nbt.Path → Literal
  | decimal : Float → Literal

public def Literal.check : Literal → Except Diagnostic Unit
  | .nbt value => value.2.checkSnbt.mapError fun error => .invalidCommandNbt (reprStr error)
  | .inline _ => pure ()
  | .quoted text => discard (Inline.parse ((Nbt.formatBrigadier text).pretty 120))
  | .unquoted text =>
      if Unquoted.Valid text then
        pure ()
      else throw (.invalidCommandText text)
  | .path value => do
      let text := value.format.pretty 120
      let valid := (value.head :: value.tail).all fun
        | .key key => !key.text.isEmpty
        | .index i => (Int32.ofInt i).toInt == i
        | .all => true
        | .matching p => nomatch p
      unless valid do throw (.invalidCommandText text)
      discard (Inline.parse text)
  | .decimal value => (Nbt.Value.double value).checkSnbt.mapError fun error => .invalidCommandNbt (reprStr error)

public def Literal.format : Literal → Std.Format
  | .nbt value => value.2.formatSnbt
  | .inline value => value.text
  | .unquoted text => text
  | .quoted text => Nbt.formatBrigadier text
  | .path value => value.format
  | .decimal value => Nbt.formatDecimal value

end Oria.Command
