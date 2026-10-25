module

public import Oria.NumberProvider.Core
public import Oria.NumberProvider.Error
public import Oria.Datapack.Version
public import Lean.Data.Json.Printer
public import Oria.Nbt.Format
import all Oria.NumberProvider.Core

namespace Oria.NumberProvider

@[expose] public def version : Datapack.Version := .dp121

private def Unary.name {input output : Domain} : Unary input output → String
  | .abs => "abs"
  | .negate => "negate"
  | .fromInt => "from_int"
  | .fromFloat => "from_float"
  | .ceil => "ceil"
  | .cos => "cos"
  | .floor => "floor"
  | .round => "round"
  | .sin => "sin"
  | .sqrt => "sqrt"
  | .truncate => "truncate"

private def Binary.name {domain : Domain} : Binary domain → String
  | .sub => "sub"
  | .div => "div"
  | .mod => "mod"
  | .pow => "pow"
  | .floorDiv => "floor_div"
  | .floorMod => "floor_mod"

private def Binary.fieldNames {domain : Domain} : Binary domain → String × String
  | .pow => ("base", "exponent")
  | _ => ("left", "right")

private def Aggregate.name {domain : Domain} : Aggregate domain → String
  | .add => "add"
  | .mul => "mul"
  | .minimum => "min"
  | .maximum => "max"
  | .average => "avg"
  | .length => "length"

private def checkedInt (value : Int) : Except Error Int32 :=
  if -2_147_483_648 ≤ value ∧ value ≤ 2_147_483_647 then
    pure (Int32.ofInt value)
  else throw (.intConstantOutOfRange value)

private def checkedFloat (value : Float32) : Except Error Lean.JsonNumber :=
  match Lean.JsonNumber.fromFloat? value.toFloat with
  | .inl rendered => .error (.nonFiniteFloatConstant rendered)
  | .inr number => .ok number

/-- Target operations for the shared provider fold. Integer inputs are explicit leaves;
resource references retain their identity separately from ordinary string fields. -/
public structure Encoding (v a : Type) where
  /-- Interpret an explicit integer input. -/
  input : v → Except Error a
  /-- Validate and encode an integer constant. -/
  integer : Int → Except Error a
  /-- Validate and encode a floating-point constant. -/
  floating : Float32 → Except Error a
  /-- Encode a typed resource reference. -/
  reference : Oria.ResourceId → a
  /-- Encode an ordinary string field. -/
  string : String → a
  /-- Encode a list of operands. -/
  list : List a → a
  /-- Encode the fields of a provider description. -/
  object : List (String × a) → a

private def json : Encoding Empty Lean.Json := {
  input := Empty.elim
  integer := fun value => do
    let value ← checkedInt value
    pure (.num (Lean.JsonNumber.fromInt value.toInt))
  floating := fun value => Lean.Json.num <$> checkedFloat value
  reference := fun ref => .str ref.text
  string := .str
  list := fun values => .arr values.toArray
  object := Lean.Json.mkObj
}

private def nbt : Encoding Empty Nbt.Any := {
  input := Empty.elim
  integer := fun value => do pure ⟨.int, .int (← checkedInt value)⟩
  floating := fun value => do
    discard <| checkedFloat value
    pure ⟨.float, .float value⟩
  reference := fun ref => ⟨.string, .string ref.text⟩
  string := fun value => ⟨.string, .string value⟩
  list := fun values => ⟨.list, .list (Nbt.Values.ofValues values.toArray)⟩
  object := fun fields => ⟨.compound, .compound (fields.foldr
    (fun (key, ⟨_, value⟩) rest => .cons ⟨key⟩ value rest) .nil)⟩
}

private def unary {v a : Type} (encoding : Encoding v a) (kind : String)
    (input : Except Error a) : Except Error a := do
  pure (encoding.object [("type", encoding.string s!"minecraft:{kind}"), ("input", ← input)])

private def binary {v a : Type} (encoding : Encoding v a) (kind leftName rightName : String)
    (left right : Except Error a) : Except Error a := do
  pure (encoding.object [("type", encoding.string s!"minecraft:{kind}"),
    (leftName, ← left), (rightName, ← right)])

mutual
  private def Term.encode {v a : Type} {domain : Domain} (encoding : Encoding v a) :
      Term v domain → Except Error a
    | .input value => encoding.input value
    | .intConstant value => encoding.integer value
    | .floatConstant value => encoding.floating value
    | .reference ref => pure (encoding.reference ref.id)
    | .unary operator input => unary encoding operator.name (input.encode encoding)
    | .binary operator left right =>
        let fields := operator.fieldNames
        binary encoding operator.name fields.1 fields.2 (left.encode encoding) (right.encode encoding)
    | .aggregate operator inputs => do
        pure (encoding.object [("type", encoding.string s!"minecraft:{operator.name}"),
          ("inputs", encoding.list (← inputs.encode encoding))])
    | .uniform minimum maximum => binary encoding "uniform" "min" "max"
        (minimum.encode encoding) (maximum.encode encoding)
    | .binomial n p => binary encoding "binomial" "n" "p"
        (n.encode encoding) (p.encode encoding)

  private def Terms.encode {v a : Type} {domain : Domain} (encoding : Encoding v a) :
      Terms v domain → Except Error (List a)
    | .one term => return [← term.encode encoding]
    | .cons term rest => return (← term.encode encoding) :: (← rest.encode encoding)
end

namespace Number

/-- Fold the provider through one target encoding, retaining its typed input carrier. -/
public def encode {v a : Type} {domain : Domain}
    (number : Number domain v) (encoding : Encoding v a) : Except Error a :=
  number.term.encode encoding

/-- Encode a provider for Minecraft 26.3 / Data Pack 121. -/
public def toJson {domain : Domain} (number : Number domain) : Except Error Lean.Json :=
  number.term.encode json

/-- Build a generic NBT value for composition with other SNBT data. -/
public def toNbt {domain : Domain} (number : Number domain) : Except Error Nbt.Any :=
  number.term.encode nbt

public def toSnbt {domain : Domain} (number : Number domain) : Except Error Std.Format := do
  let ⟨_, value⟩ ← number.toNbt
  pure value.formatSnbt

public def renderSnbt {domain : Domain} (number : Number domain) (width : Nat) : Except Error String :=
  number.toSnbt.map (Std.Format.pretty · width)

end Number

private def optionalBound {domain : Domain} (name : String) (bound : Option (Term Empty domain)) :
    Except Error (List (String × Lean.Json)) :=
  match bound with
  | none => return []
  | some term => return [(name, ← term.encode json)]

namespace NumberRange

public def toJson {domain : Domain} (range : NumberRange domain) : Except Error Lean.Json := do
  match range.term with
  | .exact term => term.encode json
  | .bounds minimum maximum =>
      let minimum ← optionalBound "min" minimum
      let maximum ← optionalBound "max" maximum
      pure (.mkObj (minimum ++ maximum))

end NumberRange
end Oria.NumberProvider
