module

public import Oria.Nbt.Basic
public import Std.Data.HashMap
public import Init.Data.Vector

namespace Oria.Nbt

universe u

public inductive DecodeIssue where
  | tag (expected actual : Tag)
  | missingField
  | unknownConstructor (name : String)
  | constructorKeys (count : Nat)
  | arity (expected actual : Nat)
  | boolean (value : Int8)
  deriving BEq, DecidableEq, Repr

public structure DecodeError where
  path : List PathSegment := []
  reason : DecodeIssue
  deriving BEq, DecidableEq, Repr

public class FromNbt (a : Type u) where
  fromNbt : Any → Except DecodeError a

namespace Decode

@[expose] public def fail {a : Type u} (reason : DecodeIssue) : Except DecodeError a :=
  .error ⟨[], reason⟩

@[expose] public def within {a : Type u} (step : PathSegment) (result : Except DecodeError a) :
    Except DecodeError a :=
  result.mapError fun error => {error with path := step :: error.path}

@[expose] public def expect (expected : Tag) : Any → Except DecodeError (Value expected)
  | ⟨actual, value⟩ =>
      if h : actual = expected then .ok (h ▸ value)
      else fail (.tag expected actual)

/-- Build one lookup table, with the final occurrence of a key taking precedence. -/
@[expose] public def fields : Fields → Std.HashMap String Any
  | .nil => {}
  | .cons key value rest => (fields rest).insertIfNew key.text ⟨_, value⟩

@[expose] public def record (value : Any) : Except DecodeError (Std.HashMap String Any) := do
  let .compound fs ← expect .compound value
  pure (fields fs)

@[expose] public def field {a : Type u} [FromNbt a] (fields : Std.HashMap String Any) (key : String) :
    Except DecodeError a :=
  within (.key ⟨key⟩) <| match fields[key]? with
    | none => fail .missingField
    | some value => FromNbt.fromNbt value

@[expose] public def variant (value : Any) : Except DecodeError (String × Any) := do
  let fields ← record value
  match fields.toList with
  | [field] => pure field
  | _ => fail (.constructorKeys fields.size)

@[expose] public def values : Values → List Any
  | .nil => []
  | .cons value rest => ⟨_, value⟩ :: values rest

/-- The checked arity gives generated projections ordinary `Fin` indices. -/
@[expose] public def arguments (n : Nat) (value : Any) : Except DecodeError (Vector Any n) := do
  let .list vs ← expect .list value
  let args := (values vs).toArray
  if h : args.size = n then pure ⟨args, h⟩
  else fail (.arity n args.size)

@[expose] public def element {a : Type u} {n : Nat} [FromNbt a] (args : Vector Any n) (i : Fin n) :
    Except DecodeError a :=
  within (.index i.val) (FromNbt.fromNbt args[i])

end Decode

public instance : FromNbt Any where
  fromNbt := .ok

public instance {t : Tag} : FromNbt (Value t) where
  fromNbt := Decode.expect t

public instance : FromNbt Int8 where
  fromNbt value := do let .byte n ← Decode.expect .byte value; pure n

public instance : FromNbt Int16 where
  fromNbt value := do let .short n ← Decode.expect .short value; pure n

public instance : FromNbt Int32 where
  fromNbt value := do let .int n ← Decode.expect .int value; pure n

public instance : FromNbt Int64 where
  fromNbt value := do let .long n ← Decode.expect .long value; pure n

public instance : FromNbt Float32 where
  fromNbt value := do let .float n ← Decode.expect .float value; pure n

public instance : FromNbt Float where
  fromNbt value := do let .double n ← Decode.expect .double value; pure n

public instance : FromNbt String where
  fromNbt value := do let .string s ← Decode.expect .string value; pure s

public instance : FromNbt Bool where
  fromNbt value := do
    let .byte n ← Decode.expect .byte value
    if n = 0 then pure false
    else if n = 1 then pure true
    else Decode.fail (.boolean n)

public instance : FromNbt Unit where
  fromNbt value := do let .compound _ ← Decode.expect .compound value; pure ()

@[expose] public def Decode.list {a : Type u} [FromNbt a] : Values → Nat → Except DecodeError (List a)
  | .nil, _ => pure []
  | .cons value rest, i => do
      let value ← Decode.within (.index i) (FromNbt.fromNbt ⟨_, value⟩)
      let rest ← Decode.list rest (i + 1)
      pure (value :: rest)

public instance {a : Type u} [FromNbt a] : FromNbt (List a) where
  fromNbt value := (Decode.expect .list value).bind fun (.list vs) => Decode.list vs 0

public instance {a : Type u} [FromNbt a] : FromNbt (Array a) where
  fromNbt value := (FromNbt.fromNbt (a := List a) value).map List.toArray

public instance {a : Type u} [FromNbt a] : FromNbt (Option a) where
  fromNbt value := (Decode.variant value).bind fun (name, raw) =>
    Decode.within (.key ⟨name⟩) <| match name with
      | "none" => (Decode.arguments 0 raw).map fun _ => none
      | "some" => (Decode.arguments 1 raw).bind fun args =>
          (Decode.element args ⟨0, by decide⟩).map some
      | _ => Decode.fail (.unknownConstructor name)

end Oria.Nbt
