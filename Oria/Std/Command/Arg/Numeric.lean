module

public import Oria.Command.Codec
public import Init.Data.OfScientific

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Numeric command arguments

`Scalar` supplies integer parameters. `Decimal` also accepts construction-time fractional
values for coordinates and angles. Integer spelling is retained by static and dynamic I32
cases; the decimal case retains a decimal point for integral values, including zero.
Minecraft uses that distinction when centering absolute world coordinates.
`Duration` combines a finite Scalar count with the native infinite token. The receiving
command determines the finite count's unit and bounds.
`Time` encodes ticks, seconds, or days for commands using Minecraft's time parser. It supports
fractional host counts and runtime I32 counts, with native Float32 rounding to ticks.

Integer literals and host `Int32` values enter `Scalar` and `Decimal` with integer spelling.
Runtime `Val Int32` expressions introduce macro holes. Decimal and scientific literals, host
`Float`, and host `Float32` values enter `Decimal` with fractional spelling. Thus `1` and `1.0`
remain distinct coordinates; negation preserves the argument's static or dynamic form.
-/

namespace Oria.Std.Command.Arg

/-- An integer parameter supplied statically or through an I32 macro hole. -/
public inductive Scalar where
  /-- Integer known during construction. -/
  | static : Int32 → Scalar
  /-- Object integer evaluated at the command's execution point. -/
  | dynamic : Val Int32 → Scalar

public instance (n : Nat) : OfNat Scalar n where
  ofNat := .static (Int32.ofNat n)

public instance : Coe Int32 Scalar where
  coe := .static

public instance {r : Region} : CoeHead (Val Int32 r) Scalar where
  coe n := .dynamic n

public instance : Neg Scalar where
  neg
    | .static n => .static (-n)
    | .dynamic n => .dynamic (-n)

/-- Native finite-count or infinite duration syntax. The receiving command defines
the unit and range of a finite count. -/
public inductive Duration where
  /-- A static or runtime integer count in the command's native unit. -/
  | finite : Scalar → Duration
  /-- The native infinite duration token. -/
  | infinite

/-- Numeric argument spelling, including host-side fractional values. -/
public inductive Decimal where
  /-- Preserve native integer spelling and its coordinate-centering behavior. -/
  | static : Int32 → Decimal
  /-- Preserve integer macro serialization for a runtime value. -/
  | dynamic : Val Int32 → Decimal
  /-- Exact host floating-point value, with fractional spelling even when integral.
  Command planning rejects non-finite values. -/
  | decimal : Float → Decimal

public instance (n : Nat) : OfNat Decimal n where
  ofNat := .static (Int32.ofNat n)

public instance : OfScientific Decimal where
  ofScientific m s e := .decimal (OfScientific.ofScientific m s e : Float)

public instance : Coe Float Decimal where
  coe := .decimal

public instance : Coe Float32 Decimal where
  coe n := .decimal n.toFloat

public instance : Neg Decimal where
  neg
    | .static n => .static (-n)
    | .dynamic n => .dynamic (-n)
    | .decimal n => .decimal (-n)

/-- Native time arguments with explicit units. Minecraft parses a Float32 count and rounds
the scaled result to ticks; each receiving command specifies its minimum. -/
public inductive Time where
  /-- Game ticks. -/
  | ticks : Decimal → Time
  /-- Seconds, at 20 game ticks per second. -/
  | seconds : Decimal → Time
  /-- Game days, at 24000 ticks per day. -/
  | days : Decimal → Time

public instance : Coe Scalar Decimal where
  coe
    | .static n => .static n
    | .dynamic n => .dynamic n

public instance : Oria.Command.ArgCodec Scalar where
  key := ⟨`minecraft.argument.i32⟩
  encode
    | .static n => .i32 n
    | .dynamic n => .hole .i32 n

public instance : Oria.Command.ArgCodec Duration where
  key := ⟨`minecraft.argument.duration⟩
  encode
    | .finite n => (Oria.Command.encode n).fragment
    | .infinite => .token "infinite"

public instance : Oria.Command.ArgCodec Float where
  key := ⟨`minecraft.argument.double⟩
  encode value := ⟨[.literal (.decimal value)], Req.none⟩

public instance : Oria.Command.ArgCodec Float32 where
  key := ⟨`minecraft.argument.float⟩
  encode value := ⟨[.literal (.decimal value.toFloat)], Req.none⟩

public instance : Oria.Command.ArgCodec Decimal where
  key := ⟨`minecraft.argument.decimal⟩
  encode value :=
    let fragment : Oria.Command.Fragment EncodedVal := match value with
      | .static n => .i32 n
      | .dynamic n => .hole .i32 n
      | .decimal n =>
          let fragment := (Oria.Command.encode n).fragment
          if n.toBits != 0x8000000000000000 && n == n.floor then
            fragment.append (.token ".0")
          else fragment
    ⟨fragment.segments, Req.none⟩

public instance : Oria.Command.ArgCodec Time where
  key := ⟨`minecraft.argument.time⟩
  encode time :=
    let (value, unit) : Decimal × Oria.Command.SyntaxToken := match time with
      | .ticks value => (value, "t")
      | .seconds value => (value, "s")
      | .days value => (value, "d")
    let fragment := (Oria.Command.encode value).fragment.append (.token unit)
    ⟨fragment.segments, Req.none⟩

@[simp] public theorem Time.encode_requirements (time : Time) :
    (Oria.Command.encode time).requirements = Req.none := rfl

@[simp] public theorem Time.encode_fragment_requirements (time : Time) :
    (Oria.Command.encode time).fragment.requirements = Req.none := rfl

namespace Scalar

/-- Encoding numeric values reads no implicit execution context. -/
@[expose] public def requirements (_ : Scalar) : ReqRow := Req.none

@[simp] public theorem encode_requirements (value : Scalar) :
    (Oria.Command.encode value).requirements = Req.none := by cases value <;> rfl

@[simp] public theorem encode_fragment_requirements (value : Scalar) :
    (Oria.Command.encode value).fragment.requirements = Req.none := by cases value <;> rfl

end Scalar

namespace Duration

@[simp] public theorem encode_requirements (value : Duration) :
    (Oria.Command.encode value).requirements = Req.none := by
  cases value with
  | finite n => exact Scalar.encode_requirements n
  | infinite => rfl

@[simp] public theorem encode_fragment_requirements (value : Duration) :
    (Oria.Command.encode value).fragment.requirements = Req.none := encode_requirements value

end Duration

namespace Decimal

@[simp] public theorem encode_requirements (value : Decimal) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem encode_fragment_requirements (value : Decimal) :
    (Oria.Command.encode value).fragment.requirements = Req.none := encode_requirements value

end Decimal

namespace Float

@[simp] public theorem encode_requirements (value : Float) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem encode_fragment_requirements (value : Float) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

end Float

namespace Float32

@[simp] public theorem encode_requirements (value : Float32) :
    (Oria.Command.encode value).requirements = Req.none := rfl

@[simp] public theorem encode_fragment_requirements (value : Float32) :
    (Oria.Command.encode value).fragment.requirements = Req.none := rfl

end Float32

end Oria.Std.Command.Arg
