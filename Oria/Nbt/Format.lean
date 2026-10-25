module

public import Oria.Nbt.Basic
public import Lean.Data.Json.Printer
public import Init.Data.Format.Basic

namespace Oria.Nbt

open Std Std.Format

variable {tag : Tag}

private def quoted (value : String) : Format :=
  -- Escaping '$' also keeps a literal independent of function-macro substitution.
  (Lean.Json.renderString value).replace "$" "\\u0024"

public def Key.format (key : Key) : Format := quoted key.text

/-- Exact decimal form shared by SNBT numbers and command scale arguments. -/
public def formatDecimal (value : Float) : Format :=
  if !value.isFinite then toString value
  else if value.toBits == 0x8000000000000000 then "-0.0"
  else if value == 0 then "0"
  else
    -- Brigadier requires fixed-point text. JsonNumber supplies decimal normalization;
    -- its scientific-notation printer is unsuitable for command arguments.
    let (m, e) := value.frExp
    let n := (m.abs.scaleB 53).toUInt64.toNat
    let n : Int := if value < 0 then -(n : Int) else n
    let number : Lean.JsonNumber := match e - 53 with
      | .ofNat k => ⟨n * (2 ^ k : Nat), 0⟩
      | .negSucc k => ⟨n * (5 ^ (k + 1) : Nat), k + 1⟩
    let (sign, mantissa, point) := number.normalize
    let digits := toString mantissa
    let zeroes n : Format := String.ofList (List.replicate n '0')
    let magnitude : Format := match point with
      | .negSucc n => "0." ++ zeroes (n + 1) ++ digits
      | .ofNat n =>
        if digits.length ≤ n then digits ++ zeroes (n - digits.length)
        else Std.Format.text (if n == 0 then "0" else (digits.take n).toString) ++
          "." ++ (digits.drop n).toString
    Std.Format.text (if sign < 0 then "-" else "") ++ magnitude

private def collection (multiline : Bool) (left right : String) (values : List Format) : Format :=
  if values.isEmpty then left ++ right
  else if multiline then
    group (left ++ nest 2 (line ++ joinSep values ("," ++ line)) ++ line ++ right)
  else left ++ joinSep values "," ++ right

mutual
  private def formatValue (multiline : Bool) : {t : Tag} → Value t → Format
    | _, .byte v => toString v ++ "b"
    | _, .short v => toString v ++ "s"
    | _, .int v => toString v
    | _, .long v => toString v ++ "L"
    | _, .float v => formatDecimal v.toFloat ++ "f"
    | _, .double v => formatDecimal v ++ "d"
    | _, .string v => quoted v
    | _, .byteArray vs => collection multiline "[B;" "]" (vs.toList.map fun v => toString v ++ "b")
    | _, .intArray vs => collection multiline "[I;" "]" (vs.toList.map (toString ·))
    | _, .longArray vs => collection multiline "[L;" "]" (vs.toList.map fun v => toString v ++ "L")
    | _, .list vs => collection multiline "[" "]" (formatValues multiline vs)
    | _, .compound fs => collection multiline "{" "}" (formatFields multiline fs)

  private def formatValues (multiline : Bool) : Values → List Format
    | .nil => []
    | .cons v vs => formatValue multiline v :: formatValues multiline vs

  private def formatFields (multiline : Bool) : Fields → List Format
    | .nil => []
    | .cons key value rest =>
        (key.format ++ ":" ++ (if multiline then " " else "") ++ formatValue multiline value) ::
          formatFields multiline rest
end

/-- A width-sensitive document for inspection. -/
public def Value.format (value : Value tag) : Format := formatValue true value

/-- Compact document used inside a single command line; floats must be finite for SNBT. -/
public def Value.formatSnbt (value : Value tag) : Format := formatValue false value

public def Value.pretty (value : Value tag) (width : Nat) : String := value.format.pretty width

public inductive Error where
  | nonFiniteFloat (value : String)
  deriving BEq, DecidableEq, Repr

mutual
  public def Value.checkSnbt : {t : Tag} → Value t → Except Error Unit
    | _, .float v => if v.isFinite then pure () else throw (.nonFiniteFloat (toString v))
    | _, .double v => if v.isFinite then pure () else throw (.nonFiniteFloat (toString v))
    | _, .list values => checkValues values
    | _, .compound fields => checkFields fields
    | _, _ => pure ()

  private def checkValues : Values → Except Error Unit
    | .nil => pure ()
    | .cons value rest => Value.checkSnbt value *> checkValues rest

  private def checkFields : Fields → Except Error Unit
    | .nil => pure ()
    | .cons _ value rest => Value.checkSnbt value *> checkFields rest
end

/-- Checked, single-line SNBT. String escaping is delegated to Lean's JSON implementation. -/
public def Value.renderSnbt (value : Value tag) : Except Error String := do
  value.checkSnbt
  pure (value.formatSnbt.pretty 120)

/-- Brigadier quoted strings escape quote and backslash, as used by paths and selector names. -/
public def formatBrigadier (text : String) : Format :=
  "\"" ++ Std.Format.text ((text.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

private def segment (value : PathSegment) : Format :=
  match value with
  -- NBT paths use Brigadier's quoted strings, which escape only quote and backslash.
  | .key key => formatBrigadier key.text
  | .index i => "[" ++ toString i ++ "]"
  | .all => "[]"
  | .matching p => nomatch p

public def formatSuffix (base : Format) (suffix : List PathSegment) : Format :=
  suffix.foldl (fun doc value => match value with
    | .key _ => doc ++ "." ++ segment value
    | .index _ | .all => doc ++ segment value
    | .matching p => nomatch p) base

public def Path.format (path : Path) : Format := formatSuffix (segment path.head) path.tail

end Oria.Nbt
