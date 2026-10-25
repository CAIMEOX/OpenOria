module

public import Oria.Std.Compute
public import Oria.NumberProvider
import all Oria.Std.Command.Arg.Data
import all Oria.NumberProvider.Core
import all Oria.NumberProvider.Encode.DP121

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Typed numeric expressions

This module connects [NumberProvider](##Oria.NumberProvider) expressions to
[Compute](##Oria.Std.Compute). `Number.input` explicitly embeds an object I32 value in a
provider expression. `Calculation.inputs` checks its constants during construction and
supplies the calculation to `Compute.run`; the command's normal result is an object I32.
Ordinary Oria arithmetic retains its own semantics and compilation path.

`Calculation.ofNumber` encodes closed resource expressions. `Calculation.ofInputs` returns
host diagnostics for expressions whose constants are computed during construction.
Requirements come from constructor summaries; named resources remain conservative.
-/

namespace Oria.Std.Command.Arg

/--
Encode a provider according to its numeric domain, preserving the choice of integer or
float registry and the expression's context summary.

Runs at host construction time. Out-of-range integers, non-finite floats, and invalid
resource names produce diagnostics. Pass a successful result to
{name}`Oria.Std.Compute.run` for in-game evaluation.
-/
public def Calculation.ofNumber {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d) :
    Except Diagnostic Calculation := do
  let value ← number.toNbt.mapError fun error => .invalidCommandNbt (reprStr error)
  let provider ← match value with
    | ⟨.string, .string id⟩ =>
        Provider.named <$> (ResourceId.parse id).mapError (fun _ => .invalidResourceId id)
    | _ => pure (Provider.ofNbt value)
  let provider := provider.withRequirements number.requirements
  pure <| match d with
    | .int => .integer provider
    | .float => .float provider

/- Provider command arguments distinguish a top-level resource/constant from an inline
operand. Both forms are produced by the same fold, before command formatting. -/
private structure EncodedNumber where
  nested : Oria.Command.Fragment EncodedVal
  argument : Provider

private def encoded (fragment : Oria.Command.Fragment EncodedVal) : EncodedNumber :=
  ⟨fragment, Provider.inline fragment⟩

private def constant (value : Nbt.Any) : EncodedNumber :=
  ⟨.nbt value.2, Provider.ofNbt value⟩

private def inputsEncoding : Oria.NumberProvider.Encoding (Val Int32) EncodedNumber := {
  input := fun value => pure ⟨.hole .i32 (value : EncodedVal .i32), .scalar value⟩
  integer := fun value => constant <$> (Oria.NumberProvider.Number.intConstant value).toNbt
  floating := fun value => constant <$> (Oria.NumberProvider.Number.floatConstant value).toNbt
  reference := fun ref => ⟨.nbt (.string ref.text), Provider.named ref⟩
  string := fun value => encoded (.nbt (.string value))
  list := fun values => encoded (.nbtList (values.map (·.nested)))
  object := fun fields => encoded (.nbtCompound (fields.map fun (key, value) => (⟨key⟩, value.nested))) }

/-- Encode an explicitly staged provider expression. Each integer input becomes a typed
command-macro hole; constants and structure remain static. Integer-to-float conversion
uses the provider's `Number.fromInt` operation. Encoding errors occur during construction,
before any Minecraft command is executed. -/
public def Calculation.ofInputs {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32)) : Except Diagnostic Calculation := do
  let value ← (number.encode inputsEncoding).mapError fun error => .invalidCommandNbt (reprStr error)
  let provider : Provider := ⟨value.argument.fragment, number.requirements⟩
  pure <| match d with
    | .int => .integer provider
    | .float => .float provider

/-- The executable provider encoder succeeds on this staged expression. This proposition
checks construction-time constants; it does not inspect the values of runtime inputs. -/
@[expose] public def Calculation.InputsEncodable {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32)) : Prop :=
  match Calculation.ofInputs number with
  | .ok _ => True
  | .error _ => False

public instance {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32)) :
    Decidable (Calculation.InputsEncodable number) := by
  unfold Calculation.InputsEncodable
  split <;> infer_instance

private theorem binary_encodable {d : Oria.NumberProvider.Domain}
    (op : Oria.NumberProvider.Binary d)
    (x y : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.binary op x y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y := by
  obtain ⟨tx, rx⟩ := x
  obtain ⟨ty, ry⟩ := y
  cases hx : tx.encode inputsEncoding <;> cases hy : ty.encode inputsEncoding <;>
    simp [Calculation.InputsEncodable, Calculation.ofInputs, Oria.NumberProvider.Number.binary,
          Oria.NumberProvider.Number.encode, Oria.NumberProvider.Term.encode,
          Oria.NumberProvider.binary, hx, hy, Except.mapError, Bind.bind, Pure.pure, Except.pure, Except.bind]

private theorem pair_encodable {d : Oria.NumberProvider.Domain}
    (op : Oria.NumberProvider.Aggregate d)
    (x y : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.aggregate op x [y]) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y := by
  obtain ⟨tx, rx⟩ := x
  obtain ⟨ty, ry⟩ := y
  cases hx : tx.encode inputsEncoding <;> cases hy : ty.encode inputsEncoding <;>
    simp [Calculation.InputsEncodable, Calculation.ofInputs, Oria.NumberProvider.Number.aggregate,
          Oria.NumberProvider.Number.terms, Oria.NumberProvider.Number.encode,
          Oria.NumberProvider.Term.encode, Oria.NumberProvider.Terms.encode, hx, hy,
          Except.mapError, Bind.bind, Pure.pure, Except.pure, Except.bind]

private theorem unary_encodable {d e : Oria.NumberProvider.Domain}
    (op : Oria.NumberProvider.Unary d e)
    (x : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.unary op x) ↔
      Calculation.InputsEncodable x := by
  obtain ⟨tx, rx⟩ := x
  cases hx : tx.encode inputsEncoding <;>
    simp [Calculation.InputsEncodable, Calculation.ofInputs, Oria.NumberProvider.Number.unary,
        Oria.NumberProvider.Number.encode, Oria.NumberProvider.Term.encode,
        Oria.NumberProvider.unary, hx, Except.mapError, Bind.bind, Pure.pure, Except.pure, Except.bind]

/-- Object integer inputs have no construction-time encoding failure. -/
@[simp] public theorem Calculation.input_encodable (x : Val Int32) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.input x) :=
  private_decl% (of_decide_eq_true rfl)

/-- Integer constant validation is exactly signed I32 representability. -/
@[simp] public theorem Calculation.int_encodable (n : Int) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.intConstant n) ↔
      -2147483648 ≤ n ∧ n ≤ 2147483647 := private_decl% (by
  by_cases h : -2147483648 ≤ n ∧ n ≤ 2147483647 <;>
    simp [Calculation.InputsEncodable, Calculation.ofInputs, inputsEncoding,
    Oria.NumberProvider.Number.intConstant, Oria.NumberProvider.Number.encode,
    Oria.NumberProvider.Number.toNbt, Oria.NumberProvider.Term.encode,
    Oria.NumberProvider.nbt, Oria.NumberProvider.checkedInt, h,
    Except.mapError, Bind.bind, Pure.pure, Except.pure, Except.bind, Functor.map, Except.map,
    throw, throwThe, MonadExceptOf.throw])

/-- Integer numeral validation uses the same signed upper bound. -/
@[simp] public theorem Calculation.nat_encodable (n : Nat) :
    Calculation.InputsEncodable (no_index (OfNat.ofNat n) : Oria.NumberProvider.Number .int (Val Int32)) ↔
      n ≤ 2147483647 := private_decl% (by
  change Calculation.InputsEncodable (Oria.NumberProvider.Number.intConstant (Int.ofNat n)) ↔ _
  rw [Calculation.int_encodable]
  simp only [Int.ofNat_eq_natCast]
  omega)

/-- Division validates the constants in both operands. -/
@[simp] public theorem Calculation.div_encodable {d : Oria.NumberProvider.Domain}
    (x y : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (x / y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y :=
  private_decl% binary_encodable .div x y

/-- Subtraction validates the constants in both operands. -/
@[simp] public theorem Calculation.sub_encodable {d : Oria.NumberProvider.Domain}
    (x y : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (x - y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y :=
  private_decl% binary_encodable .sub x y

/-- Floor division validates the constants in both operands. -/
@[simp] public theorem Calculation.floorDiv_encodable
    (x y : Oria.NumberProvider.Number .int (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.floorDiv x y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y :=
  private_decl% binary_encodable .floorDiv x y

/-- Floor modulo validates the constants in both operands. -/
@[simp] public theorem Calculation.floorMod_encodable
    (x y : Oria.NumberProvider.Number .int (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.floorMod x y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y :=
  private_decl% binary_encodable .floorMod x y

/-- Binary addition validates the constants in both operands. -/
@[simp] public theorem Calculation.add_encodable {d : Oria.NumberProvider.Domain}
    (x y : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (x + y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y :=
  private_decl% pair_encodable .add x y

/-- Binary multiplication validates the constants in both operands. -/
@[simp] public theorem Calculation.mul_encodable {d : Oria.NumberProvider.Domain}
    (x y : Oria.NumberProvider.Number d (Val Int32)) :
    Calculation.InputsEncodable (x * y) ↔
      Calculation.InputsEncodable x ∧ Calculation.InputsEncodable y :=
  private_decl% pair_encodable .mul x y

/-- Integer-to-float conversion preserves construction-time validity. -/
@[simp] public theorem Calculation.fromInt_encodable
    (x : Oria.NumberProvider.Number .int (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.fromInt x) ↔
      Calculation.InputsEncodable x := private_decl% unary_encodable .fromInt x

/-- Square root preserves construction-time validity; its runtime result remains native. -/
@[simp] public theorem Calculation.sqrt_encodable
    (x : Oria.NumberProvider.Number .float (Val Int32)) :
    Calculation.InputsEncodable (Oria.NumberProvider.Number.sqrt x) ↔
      Calculation.InputsEncodable x := private_decl% unary_encodable .sqrt x

private def inputFragment {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32))
    (valid : Calculation.InputsEncodable number) : Oria.Command.Fragment EncodedVal :=
  match result : Calculation.ofInputs number with
  | .ok (.integer p) | .ok (.float p) => p.fragment
  | .error _ => False.elim (by simp [Calculation.InputsEncodable, result] at valid)

/-- Construct a staged calculation with a proof that its host encoding succeeds.
Automatic proofs cover integer inputs and numerals, binary addition, subtraction,
multiplication and division, floor division and modulo, and explicit integer-to-float
conversion followed by square root. Other provider constructors and native floating-point
constants use a supplied validity proof or host diagnostics with {name}`Calculation.ofInputs`.

```lean
open Oria Oria.Std Oria.Std.Command.Arg Oria.NumberProvider
example (n : Val Int32) : Calculation :=
  Calculation.inputs (Number.floorMod (Number.input n) 16)
```
-/
public def Calculation.inputs {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32))
    (valid : Calculation.InputsEncodable number := by
      simp +zetaDelta) : Calculation :=
  let provider : Provider := ⟨inputFragment number valid, number.requirements⟩
  match d with
  | .int => .integer provider
  | .float => .float provider

/-- The expression's constructor summary determines the calculation's context. -/
@[simp] public theorem Calculation.inputs_requirements {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32))
    (valid : Calculation.InputsEncodable number) :
    (Calculation.inputs number valid).requirements = number.requirements :=
  private_decl% (by cases d <;> rfl)

/-- The checked constructor returns exactly the successful encoding; it supplies no
fallback calculation and does not convert construction errors into runtime failure. -/
public theorem Calculation.ofInputs_inputs {d : Oria.NumberProvider.Domain}
    (number : Oria.NumberProvider.Number d (Val Int32))
    (valid : Calculation.InputsEncodable number) :
    Calculation.ofInputs number = .ok (Calculation.inputs number valid) := private_decl% (by
  cases result : number.encode inputsEncoding with
  | error err => simp [Calculation.InputsEncodable, Calculation.ofInputs, result, Except.mapError, Bind.bind, Except.bind] at valid
  | ok value =>
    cases d
    · have h : Calculation.ofInputs number = .ok (.integer ⟨value.argument.fragment, number.requirements⟩) := by
        simp [Calculation.ofInputs, result, Except.mapError, Bind.bind, Pure.pure, Except.pure, Except.bind]
      simp only [Calculation.inputs, inputFragment]
      split <;> simp_all
    · have h : Calculation.ofInputs number = .ok (.float ⟨value.argument.fragment, number.requirements⟩) := by
        simp [Calculation.ofInputs, result, Except.mapError, Bind.bind, Pure.pure, Except.pure, Except.bind]
      simp only [Calculation.inputs, inputFragment]
      split <;> simp_all)

end Oria.Std.Command.Arg

namespace Oria.Std.Compute

open Oria.Std.Command.Arg

/-- Evaluate an explicitly constructed provider expression with typed integer inputs.
Construction-time checks and the context summary are discharged before command lowering.
Runtime division, rounding, overflow, and failure follow the selected native provider.
Automatic validity proofs follow {name}`Calculation.inputs`. -/
public def runInputs {d : Oria.NumberProvider.Domain} (context : ComputeContext)
    (number : Oria.NumberProvider.Number d (Val Int32))
    (valid : Calculation.InputsEncodable number := by simp +zetaDelta) :
    Prog (grade context number.requirements) Int32 := by
  simpa only [Calculation.inputs_requirements] using run context (Calculation.inputs number valid)

end Oria.Std.Compute
