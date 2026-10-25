module

public import Oria.Nbt.Encode
public import Oria.Nbt.Decode
public import Oria.Nbt.Description
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public meta import Oria.Nbt.Encode
public meta import Oria.Nbt.Decode
public meta import Oria.Nbt.Description
meta import all Oria.Nbt.Description

namespace Oria.Nbt.Deriving

open Lean Meta Elab Command Lean.Elab.Deriving
open Lean.Parser.Term

private meta structure Shape where
  type : InductiveVal
  constructors : Array ConstructorVal
  fields : Option (Array Name)
  enumeration : Bool

private meta def inspect (name : Name) : TermElabM Shape := do
  let type ← getConstInfoInduct name
  unless type.numIndices = 0 do
    throwError "NBT deriving supports datatypes without indices; provide a custom instance for {name}"
  if type.isRec || type.all.length > 1 then
    throwError "NBT deriving supports non-recursive datatypes; provide a custom instance for {name}"
  let constructors ← type.ctors.toArray.mapM getConstInfoCtor
  for ctor in constructors do
    forallTelescopeReducing ctor.type fun xs _ => do
      let mut previous := #[]
      for x in xs[type.numParams...*] do
        let fieldType ← inferType x
        if ← isProp fieldType then
          throwError "NBT deriving requires a custom instance for proof-bearing fields"
        if fieldType.hasAnyFVar (previous.contains ·) then
          throwError "NBT deriving requires a custom instance for dependent fields"
        previous := previous.push x.fvarId!
  let env ← getEnv
  let fields := if isStructure env name then
      some (getStructureFieldsFlattened env name (includeSubobjectFields := false))
    else none
  let labels := (fields.getD (constructors.map (·.name))).map (·.eraseMacroScopes.getString!)
  unless labels.toList.eraseDups.length = labels.size do
    throwError "NBT deriving requires distinct field or constructor labels"
  pure ⟨type, constructors, fields, constructors.all (·.numFields == 0)⟩

private meta def label (name : Name) : String := name.eraseMacroScopes.getString!

private meta def fresh (n : Nat) : TermElabM (Array Ident) :=
  (List.range n).toArray.mapM fun _ => return mkIdent (← mkFreshUserName `x)

private meta def encode (shape : Shape) (target : Ident) (typed := false) : TermElabM Term := do
  let enc : Term ← if typed then `((@Nbt.ToNbt.toNbt _ Nbt.Repr.toToNbt)) else `(Nbt.ToNbt.toNbt)
  if let some fields := shape.fields then
    let fields ← fields.mapM fun field =>
      `(($(quote (label field)), $enc $target.$(mkIdent field)))
    return ← `(Nbt.Encode.record [$fields,*])
  let params ← (List.range shape.type.numParams).toArray.mapM fun _ => `(_)
  let alts ← shape.constructors.mapM fun ctor => do
    let args ← fresh ctor.numFields
    let pattern ← `(@$(mkCIdent ctor.name) $params:term* $args:ident*)
    let body ← if shape.enumeration then
        `((⟨.string, .string $(quote (label ctor.name))⟩ : Nbt.Any))
      else
        let values ← args.mapM fun arg => `($enc $arg)
        `(Nbt.Encode.variant $(quote (label ctor.name)) [$values,*])
    `(matchAltExpr| | $pattern:term => $body:term)
  `(match $target:term with $alts:matchAlt*)

/-- Explicit Except.bind composes fields living in different universes. -/
private meta def binds (names : Array Ident) (readers : Array Term) (body : Term) :
    TermElabM Term :=
  (names.zip readers).foldrM (init := body) fun (name, reader) rest =>
    `(($reader).bind fun $name => $rest)

private meta def decode (shape : Shape) (header : Header) (input : Ident) (typed := false) : TermElabM Term := do
  if let some fields := shape.fields then
    let table := mkIdent (← mkFreshUserName `fields)
    let names ← fresh fields.size
    let keys := fields.map mkIdent
    let readers ← fields.mapM fun field => if typed then
        `(@Nbt.Decode.field _ Nbt.Repr.toFromNbt $table $(quote (label field)))
      else `(Nbt.Decode.field $table $(quote (label field)))
    let body ← `(Except.ok { $[$keys:ident := $names:ident],* })
    let body ← binds names readers body
    return ← `((Nbt.Decode.record $input).bind fun $table => $body)
  let name := mkIdent (← mkFreshUserName `name)
  let raw := mkIdent (← mkFreshUserName `raw)
  let alts ← shape.constructors.mapM fun ctor => do
    let names ← fresh ctor.numFields
    let params := header.argNames.map mkIdent
    let body ← `(Except.ok (@$(mkCIdent ctor.name) $params:ident* $names:ident*))
    let body ← if shape.enumeration then pure body else do
      let args := mkIdent (← mkFreshUserName `args)
      let readers ← (List.range ctor.numFields).toArray.mapM fun i => if typed then
          `(@Nbt.Decode.element _ _ Nbt.Repr.toFromNbt $args ⟨$(quote i), by decide⟩)
        else `(Nbt.Decode.element $args ⟨$(quote i), by decide⟩)
      let body ← binds names readers body
      `(Nbt.Decode.within (.key ⟨$(quote (label ctor.name))⟩)
          ((Nbt.Decode.arguments $(quote ctor.numFields) $raw).bind fun $args => $body))
    `(matchAltExpr| | $(quote (label ctor.name)):str => $body)
  let fallback ← `(matchAltExpr| | _ => Nbt.Decode.fail (.unknownConstructor $name))
  let alts := alts.push fallback
  let body ← `(match $name:term with $alts:matchAlt*)
  if shape.enumeration then
    `((Nbt.Decode.expect .string $input).bind fun (.string $name) => $body)
  else
    `((Nbt.Decode.variant $input).bind fun ($name, $raw) => $body)

private meta def commands (className : Name) (shape : Shape) (typed := false) : TermElabM (Array Command) := do
  let encoding := className == `Oria.Nbt.ToNbt
  let ctx ← mkContext className (if encoding then "toNbt" else "fromNbt") shape.type.name
  let header ← mkHeader (if typed then ``Nbt.Repr else className) (if encoding then 1 else 0) shape.type
  let name := mkIdent ctx.auxFunNames[0]!
  let (binders, result, body) ← if encoding then do
      let body ← encode shape (mkIdent header.targetNames[0]!) typed
      pure (header.binders, ← `(Nbt.Any), body)
    else do
      let input := mkIdent (← mkFreshUserName `input)
      let binder ← `(Lean.Parser.Term.bracketedBinderF| ($input : Nbt.Any))
      let body ← decode shape header input typed
      pure (header.binders.push binder, ← `(Except Nbt.DecodeError $(header.targetType)), body)
  let definition ← `(def $name:ident $binders:bracketedBinder* : $result := $body)
  if typed then
    let header ← mkHeader ``Nbt.Repr 0 shape.type
    let bs := header.binders
    let target := header.targetType
    let inst ← if encoding then
        `(instance $bs:bracketedBinder* : Nbt.ToNbt $target where toNbt := $name)
      else `(instance $bs:bracketedBinder* : Nbt.FromNbt $target where fromNbt := $name)
    return #[definition, inst]
  return #[definition] ++ (← mkInstanceCmds ctx className #[shape.type.name])

private meta def derive (className : Name) (names : Array Name) : CommandElabM Bool := do
  unless names.size > 0 && (← names.allM isInductive) do return false
  for name in names do
    withoutExposeFromCtors name do
      let generated ← liftTermElabM do commands className (← inspect name)
      generated.forM elabCommand
  return true

private meta def instantiateType (xs : Array Expr) (type : Expr) (args : Array Ident) : TermElabM Term :=
  withNewBinderInfos (xs.map fun x => (x.fvarId!, .default)) do
    let term ← withOptions (·.setBool `pp.funBinderTypes true) <|
      Lean.PrettyPrinter.delab (← mkLambdaFVars xs type)
    `($term $args*)

private meta def recordField (shape : Shape) (field : Name) (args : Array Ident) :
    TermElabM (Term × Term) :=
  forallTelescopeReducing shape.type.type fun xs _ => do
    let target := mkAppN (mkConst shape.type.name (shape.type.levelParams.map mkLevelParam)) xs
    withLocalDeclD `v target fun v => do
      let projection ← mkProjection v field
      let type ← instantiateType xs (← inferType projection) args
      let get ← instantiateType xs (← mkLambdaFVars #[v] projection) args
      return (get, type)

private meta def schema (shape : Shape) (header : Header) : TermElabM Term := do
  let parameters := header.argNames.map mkIdent
  if let some fields := shape.fields then
    let entries ← fields.mapM fun field => do
      let (_, ty) ← recordField shape field parameters
      `(($(quote (label field)), (Nbt.Repr.schema (a := $ty))))
    return ← `(Nbt.Schema.record [$entries,*])
  let constructors ← shape.constructors.mapM fun ctor => do
    let types ← forallTelescopeReducing ctor.type fun xs _ =>
      xs[shape.type.numParams...*].toArray.mapM fun x => do
        let ty ← inferType x
        let params := xs[:shape.type.numParams].toArray
        instantiateType params ty parameters
    pure (ctor, types)
  if shape.enumeration then
    let labels : Array Term := shape.constructors.map fun ctor => quote (label ctor.name)
    return ← `(Nbt.Schema.enumeration [$labels,*])
  let cases ← constructors.mapM fun (ctor, types) => do
    let types ← types.mapM fun ty => `(Nbt.Repr.schema (a := $ty))
    `(($(quote (label ctor.name)), [$types,*]))
  `(Nbt.Schema.variant [$cases,*])

private meta def deriveRepr (names : Array Name) : CommandElabM Bool := do
  for name in names do
    let shape ← liftTermElabM (inspect name)
    let mut definitions : Array Term := #[]
    for cls in [``ToNbt, ``FromNbt] do
      let (generated, definition) ← liftTermElabM do
        let ctx ← mkContext cls (if cls == ``ToNbt then "toNbt" else "fromNbt") shape.type.name
        pure (← commands cls shape true, mkIdent ctx.auxFunNames[0]!)
      generated.forM elabCommand
      definitions := definitions.push definition
    let command ← liftTermElabM do
      let header ← mkHeader ``Nbt.Repr 0 shape.type
      let code ← schema shape header
      let target := header.targetType
      let bs := header.binders
      let enc ← `(Lean.Parser.Tactic.simpLemma| $(definitions[0]!):term)
      let dec ← `(Lean.Parser.Tactic.simpLemma| $(definitions[1]!):term)
      let encode := definitions[0]!
      let decode := definitions[1]!
      let mk := mkCIdent ``Nbt.Repr.mk
      `(instance $bs:bracketedBinder* : Nbt.Repr $target :=
        $mk $code (by
          intro v
          change $decode ($encode v) = Except.ok v
          cases v <;>
            simp [$enc, $dec, Decode.field, Decode.record,
              Encode.record, Decode.fields, Decode.arguments, Decode.element,
              Encode.list, Decode.values, bind, pure, Except.bind, Except.pure,
              Std.HashMap.getElem?_insertIfNew, Std.HashMap.getElem_insertIfNew,
              Std.HashMap.mem_insertIfNew, Nbt.Repr.roundTrip]))
    elabCommand command
    if let some fields := shape.fields then
      let generated ← liftTermElabM do
        let header ← mkHeader ``Nbt.Repr 0 shape.type
        let target := header.targetType
        let bs := header.binders
        let params := header.argNames.map mkIdent
        let enc ← `(Lean.Parser.Tactic.simpLemma| $(definitions[0]!):term)
        let dec ← `(Lean.Parser.Tactic.simpLemma| $(definitions[1]!):term)
        let encode := definitions[0]!
        let mk := mkCIdent ``Nbt.Field.mk
        fields.mapM fun field => do
          let (f, fieldType) ← recordField shape field params
          let owner := (privateToUserName? name).getD name
          let name := mkIdent (`_root_ ++ owner ++ `Nbt ++ .mkSimple (label field))
          `(def $name:ident $bs:bracketedBinder* {i : Type} : Nbt.Access i $target $fieldType :=
            Nbt.Access.field ($mk ⟨$(quote (label field))⟩ $f (by
              intro v
              change (Decode.record ($encode v) >>= fun fs => @Decode.field _ Nbt.Repr.toFromNbt fs $(quote (label field))) = Except.ok ($f v)
              cases v
              simp [$enc, $dec, Decode.field, Decode.record, Encode.record,
                Decode.fields, bind, pure, Except.bind, Except.pure,
                Std.HashMap.getElem?_insertIfNew, Std.HashMap.getElem_insertIfNew,
                Std.HashMap.mem_insertIfNew, Nbt.Repr.roundTrip])))
      generated.forM elabCommand
  return true

meta initialize
  registerDerivingHandler `Oria.Nbt.ToNbt (derive `Oria.Nbt.ToNbt)
  registerDerivingHandler `Oria.Nbt.FromNbt (derive `Oria.Nbt.FromNbt)
  registerDerivingHandler `Oria.Nbt.Repr deriveRepr

end Oria.Nbt.Deriving
