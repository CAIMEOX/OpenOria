module

public import Oria.Nbt.Encode
public meta import Oria.Nbt.Encode
public meta import Lean

public section

namespace Oria.Nbt

declare_syntax_cat nbt (behavior := symbol)
syntax "true" : nbt
syntax "false" : nbt
syntax str : nbt
syntax "-"? num : nbt
syntax "-"? scientific : nbt
syntax "-"? num noWs ident : nbt
syntax "-"? scientific noWs ident : nbt
syntax "[" nbt,* "]" : nbt
syntax "[" &"B" ";" nbt,* "]" : nbt
syntax "[" &"I" ";" nbt,* "]" : nbt
syntax "[" &"L" ";" nbt,* "]" : nbt
syntax nbtKey := ident <|> str
syntax nbtField := nbtKey ":" nbt
syntax "{" nbtField,* "}" : nbt
syntax "nbt% " nbt : term

open Lean

private meta def integerTag (suffix : String) : Option Tag :=
  match suffix.toLower with
  | "b" => some .byte
  | "s" => some .short
  | "i" => some .int
  | "l" => some .long
  | _ => none

private meta def bits : Tag → Nat
  | .byte => 8 | .short => 16 | .int => 32 | .long => 64 | _ => 0

private meta def signed (negative : Bool) (n : TSyntax `num) : Int :=
  if negative then -Int.ofNat n.getNat else Int.ofNat n.getNat

private meta def integerTerm (tag : Tag) (negative : Bool) (n : TSyntax `num) :
    MacroM (TSyntax `term) := do
  let value := signed negative n
  let bound := (2 : Int) ^ (bits tag - 1)
  unless -bound ≤ value ∧ value < bound do
    Macro.throwErrorAt n s!"NBT integer literal is outside the signed {bits tag}-bit range"
  let term : TSyntax `term := ⟨n.raw⟩
  if negative then `(-$term) else pure term

private meta def integer (tag : Tag) (negative : Bool) (n : TSyntax `num) :
    MacroM (TSyntax `term) := do
  let value ← integerTerm tag negative n
  match tag with
  | .byte => `(Nbt.Value.byte $value)
  | .short => `(Nbt.Value.short $value)
  | .int => `(Nbt.Value.int $value)
  | .long => `(Nbt.Value.long $value)
  | _ => Macro.throwUnsupported

private meta def withSuffix (negative : Bool) (n : TSyntax `num) (suffix : TSyntax `ident) :
    MacroM (TSyntax `term) := do
  match integerTag suffix.getId.toString with
  | some tag => integer tag negative n
  | none =>
      let term : TSyntax `term := ⟨n.raw⟩
      let term ← if negative then `(-$term) else pure term
      match suffix.getId.toString.toLower with
      | "f" =>
          unless (Float32.ofNat n.getNat).isFinite do
            Macro.throwErrorAt n "SNBT does not support non-finite floating-point literals"
          `(Nbt.Value.float $term)
      | "d" =>
          unless (Float.ofNat n.getNat).isFinite do
            Macro.throwErrorAt n "SNBT does not support non-finite floating-point literals"
          `(Nbt.Value.double $term)
      | _ => Macro.throwErrorAt suffix "expected an NBT suffix: b, s, i, L, f, or d"

private meta def floating (negative single : Bool) (n : TSyntax `scientific) :
    MacroM (TSyntax `term) := do
  let (mantissa, sign, exponent) := n.getScientific
  let finite := if single then
      (OfScientific.ofScientific mantissa sign exponent : Float32).isFinite
    else (OfScientific.ofScientific mantissa sign exponent : Float).isFinite
  unless finite do Macro.throwErrorAt n "SNBT does not support non-finite floating-point literals"
  let term : TSyntax `term := ⟨n.raw⟩
  let term ← if negative then `(-$term) else pure term
  if single then `(Nbt.Value.float $term) else `(Nbt.Value.double $term)

private meta def floatingSuffix (negative : Bool) (n : TSyntax `scientific) (suffix : TSyntax `ident) :
    MacroM (TSyntax `term) :=
  match suffix.getId.toString.toLower with
  | "f" => floating negative true n
  | "d" => floating negative false n
  | _ => Macro.throwErrorAt suffix "expected f or d after a floating-point literal"

private meta def arrayElement (tag : Tag) (item : TSyntax `nbt) : MacroM (TSyntax `term) := do
  if item.raw.isAntiquot then return ⟨item.raw.getAntiquotTerm⟩
  let (negative, number, suffix) ← match item with
    | `(nbt| $n:num) => pure (false, n, none)
    | `(nbt| -$n:num) => pure (true, n, none)
    | `(nbt| $n:num$s:ident) => pure (false, n, some s)
    | `(nbt| -$n:num$s:ident) => pure (true, n, some s)
    | _ => Macro.throwErrorAt item "expected an integer literal or a typed splice in an NBT array"
  if let some suffix := suffix then
    let some source := integerTag suffix.getId.toString
      | Macro.throwErrorAt suffix "expected an integer suffix in an NBT array"
    unless bits source ≤ bits tag do
      Macro.throwErrorAt suffix "the element's integer type is wider than the NBT array type"
    discard <| integerTerm source negative number
  integerTerm tag negative number

macro_rules
  | `(nbt% true) => `(Nbt.Value.byte (1 : Int8))
  | `(nbt% false) => `(Nbt.Value.byte (0 : Int8))
  | `(nbt% $s:str) => `(Nbt.Value.string $s)
  | `(nbt% $n:num) => integer .int false n
  | `(nbt% -$n:num) => integer .int true n
  | `(nbt% $n:num$s:ident) => withSuffix false n s
  | `(nbt% -$n:num$s:ident) => withSuffix true n s
  | `(nbt% $n:scientific) => floating false false n
  | `(nbt% -$n:scientific) => floating true false n
  | `(nbt% $n:scientific$s:ident) => floatingSuffix false n s
  | `(nbt% -$n:scientific$s:ident) => floatingSuffix true n s
  | `(nbt% [$[$items],*]) => do
      let values ← items.foldrM (init := ← `(Nbt.Values.nil)) fun item rest =>
        `(Nbt.Values.cons (nbt% $item) $rest)
      `(Nbt.Value.list $values)
  | `(nbt% [B; $[$items],*]) => do
      let values ← items.mapM (arrayElement .byte)
      `(Nbt.Value.byteArray #[$values,*])
  | `(nbt% [I; $[$items],*]) => do
      let values ← items.mapM (arrayElement .int)
      `(Nbt.Value.intArray #[$values,*])
  | `(nbt% [L; $[$items],*]) => do
      let values ← items.mapM (arrayElement .long)
      `(Nbt.Value.longArray #[$values,*])
  | `(nbt% {$[$keys:nbtKey : $values:nbt],*}) => do
      let keys ← keys.mapM fun
        | `(nbtKey| $key:ident) => pure (quote key.getId.toString)
        | `(nbtKey| $key:str) => pure key
        | _ => Macro.throwUnsupported
      let fields ← (keys.zip values).foldrM (init := ← `(Nbt.Fields.nil)) fun (key, value) rest =>
        `(Nbt.Fields.cons (Nbt.Key.mk $key) (nbt% $value) $rest)
      `(Nbt.Value.compound $fields)
  | `(nbt% $value) =>
      if value.raw.isAntiquot then
        let term : TSyntax `term := ⟨value.raw.getAntiquotTerm⟩
        `((Nbt.ToNbt.toNbt $term).2)
      else Macro.throwUnsupported

end Oria.Nbt
