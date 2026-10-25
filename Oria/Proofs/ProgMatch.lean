module

public import Oria.Compiler.Definition
public import Oria.Meta.Elab.ProgMatch
import Oria.IR.Cont.Pretty
import Oria.IR.Tree.Pretty
import Oria.Proofs.McFunctionUtil
public import Oria.Proofs.Fixtures.MaybeI32
public import Oria.Proofs.Fixtures.Envelope
meta import Oria.Compiler.Definition
meta import Oria.IR.Cont.Pretty
meta import Oria.IR.Tree.Pretty
meta import Oria.Proofs.McFunctionUtil
meta import Oria.Proofs.Fixtures.MaybeI32
meta import Oria.Proofs.Fixtures.Envelope

namespace Oria.Proofs.ProgMatch

open Oria
open Lean Lean.Elab Command
open Oria.Proofs.Fixtures
open Oria.Proofs.McFunctionUtil

@[mcfunction]
private def flatTailMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0
    | .some payload => return payload

@[mcfunction]
private def wildcardTailMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .some payload => return payload
    | _ => return 0

@[mcfunction]
private def nonTailMatch
    (value : Val MaybeI32)
    (result : Val Int32) : Prog .pure Int32 :=
  do
    match value with
    | .none => Prog.pure Val.unit
    | .some _ => Prog.pure Val.unit
    return result + 1

private def nonTailMatchEarlyReturn
    (value : Val MaybeI32) : Prog .pure Unit :=
  do
    match value with
    | .none => return Val.unit
    | .some _ => Prog.pure Val.unit
    return Val.unit

/--
error: Oria `do` does not support mutable bindings
-/
#guard_msgs in
private def matchMutableBinding
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .none =>
        let mut result := I32.lit 0
        return result
    | .some payload => return payload

@[mcfunction]
private def missingConstructor
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0

@[mcfunction]
private def redundantConstructor
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0
    | .none => return 1
    | .some payload => return payload

@[mcfunction]
private def redundantAfterWildcard
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | _ => return 0
    | .some payload => return payload

@[mcfunction]
private def nestedConstructorMatch
    (value : Val Envelope) : Prog .pure Int32 :=
  do
    match value with
    | .wrap .none => return 0
    | .wrap (.some payload) => return payload

@[mcfunction]
private def twoScrutineeMatch
    (left right : Val Choice) : Prog .pure Int32 :=
  do
    match left, right with
    | .rock, .rock => return 0
    | .paper, .paper => return 1
    | _, _ => return 2

private def renderMatchPipelines
    (name : Lean.Name) : CommandElabM (String × String) := do
  let elaborated ← elaborate name
  let .ok objects := ObjectCatalog.build [
      MaybeI32.Oria.schema,
      Choice.Oria.schema,
      Envelope.Oria.schema
    ]
    | throwError "failed to build the object-match catalog"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "failed to build the object-match command catalog"
  let .ok functions := Function.Catalog.build [elaborated]
    | throwError "failed to build the object-match function catalog"
  let .ok cont := Compiler.compile functions objects commands elaborated
    | throwError "failed to lower object match `{name}`"
  return (elaborated.definition.pretty 100, cont.pretty 100)

run_cmd
  let .ok objects := ObjectCatalog.build [MaybeI32.Oria.schema]
    | throwError "object catalog failed"
  let .ok commands := Oria.Command.Catalog.build []
    | throwError "command catalog failed"
  let .ok functions := Function.Catalog.build []
    | throwError "function catalog failed"
  for (name, redundant) in [(``missingConstructor, false), (``redundantConstructor, true),
      (``redundantAfterWildcard, true)] do
    let elaborated ← elaborate name
    match Compiler.compile functions objects commands elaborated with
    | .error (.nonExhaustiveMatch _) =>
        if redundant then throwError "expected a redundant-row diagnostic"
    | .error (.redundantPattern _ _) =>
        unless redundant do throwError "expected a coverage diagnostic"
    | .error diagnostic => throwError "unexpected match diagnostic: {repr diagnostic}"
    | .ok _ => throwError "invalid matrix compiled"

/--
error: Oria `do` cannot mix host and object match discriminants
-/
#guard_msgs in
private def mixedMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    let host : Bool := true
    match value, host with
    | .none, _ => return 0
    | .some payload, _ => return payload

@[mcfunction]
private def hostMatch
    (value : Val Int32) : Prog .pure Int32 :=
  do
    let chooseOriginal : Bool := true
    match chooseOriginal with
    | true => return value
    | false => return value + 1

@[mcfunction]
private def hostOptionMatch
    (value : Val Int32) : Prog .pure Int32 :=
  do
    let choice : Option Bool := some true
    match choice with
    | some true => return value
    | _ => return value + 1

@[mcfunction]
private def literalMatch
    (value : Val Int32) : Prog .pure Int32 :=
  do
    match value with
    | 0 => return 0
    | _ => return value

@[mcfunction]
private def naturalOptionMatch
    (value : Val (Option Int32)) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0
    | .some payload => return payload

@[mcfunction]
private def explicitOptionMatch
    (value : Val (Option Int32)) : Prog .pure Int32 :=
  Oria.Option.elim value
    (Prog.pure 0)
    (fun payload => Prog.pure payload)

@[mcfunction]
private def nestedOptionMatch
    (value : Val (Option (Option Int32))) : Prog .pure Int32 :=
  do
    match value with
    | .none => return 0
    | .some .none => return 1
    | .some (.some payload) => return payload

@[mcfunction]
private def optionAndDerivedMatch
    (value : Val (Option Int32))
    (choice : Val Choice) : Prog .pure Int32 :=
  do
    match value, choice with
    | .some payload, .rock => return payload
    | .none, .paper => return 1
    | _, _ => return 2

run_cmd do
  let (naturalTree, naturalCont) ← renderMatchPipelines ``naturalOptionMatch
  let (explicitTree, explicitCont) ← renderMatchPipelines ``explicitOptionMatch
  unless naturalTree == explicitTree && naturalCont == explicitCont do
    throwError "natural Option match differs from explicit Option elimination:\nTree:\n{naturalTree}\nCont:\n{naturalCont}"

/--
error: Oria `do` object match does not support dependent matching
-/
#guard_msgs in
private def dependentObjectMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match (dependent := true) value with
    | .none => return 0
    | .some payload => return payload

/--
error: Oria `do` object match does not support generalizing
-/
#guard_msgs in
private def generalizingObjectMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match (generalizing := true) value with
    | .none => return 0
    | .some payload => return payload

/--
error: Oria `do` object match does not support a custom motive
-/
#guard_msgs in
private def motivatedObjectMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match (motive := fun _ => Prog .pure Int32) value with
    | .none => return 0
    | .some payload => return payload

/--
error: Oria `do` object match does not support named discriminants
-/
#guard_msgs in
private def namedDiscriminantMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match h : value with
    | .none => return 0
    | .some payload => return payload

/--
error: Oria `do` object match does not support `as` patterns
-/
#guard_msgs in
private def asPatternMatch
    (value : Val MaybeI32) : Prog .pure Int32 :=
  do
    match value with
    | whole@(.none) => return 0
    | .some payload => return payload

end Oria.Proofs.ProgMatch
