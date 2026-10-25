module

public import Oria
import Oria.Proofs.Fixtures.MaybeI32
import Oria.Proofs.McFunctionUtil
import Oria.IR.Tree.Pretty
meta import Oria
meta import Oria.Proofs.Fixtures.MaybeI32
meta import Oria.Proofs.McFunctionUtil
meta import Oria.IR.Tree.Pretty

namespace Oria.Proofs.Constructors

open Oria.Proofs.Fixtures

example : (Choice.rock : Prog .pure Choice) = Choice.Obj.Ctor.rock := rfl

example : (.rock : Prog .pure Choice) = Choice.Obj.Ctor.rock := rfl

private abbrev Move := Choice
example : (.rock : Prog .pure Move) = Choice.Obj.Ctor.rock := rfl

macro "rockProgram%" : term => `(Choice.rock)
example : (rockProgram% : Prog .pure Choice) = Choice.Obj.Ctor.rock := rfl
example : (rockProgram% : Choice) = Choice.rock := rfl

example (n : Val Int32) :
    (MaybeI32.some n : Prog .pure MaybeI32) = MaybeI32.Obj.Ctor.some n := rfl

example (n : Val Int32) :
    (.some n : Prog .pure MaybeI32) = MaybeI32.Obj.Ctor.some n := rfl

example : (do
    let c : Val Choice ← .rock
    return c : Prog .pure Choice) = (do
    let c ← Choice.Obj.Ctor.rock
    return c : Prog .pure Choice) := rfl

example : (do
    let c : Val Choice ← ((.rock))
    return c : Prog .pure Choice) = (do
    let c ← Choice.Obj.Ctor.rock
    return c : Prog .pure Choice) := rfl

example : (do
    let c ← Choice.rock
    return c : Prog .pure Choice) = (do
    let c ← Choice.Obj.Ctor.rock
    return c : Prog .pure Choice) := rfl

example (n : Val Int32) :
    (do return .some n : Prog .pure MaybeI32) = (do
      let x ← MaybeI32.Obj.Ctor.some n
      return x : Prog .pure MaybeI32) := rfl

example (n : Val Int32) :
    (do return MaybeI32.some n : Prog .pure MaybeI32) = (do
      let x ← MaybeI32.Obj.Ctor.some n
      return x : Prog .pure MaybeI32) := rfl

public inductive Parcel (a : Type) where
  | empty
  | item (value : a)
  deriving Oria.Object

example {a : Type} {t : ObjTy} [Object a t] (v : Val a) :
    (.item (value := v) : Prog .pure (Parcel a)) = Parcel.Obj.Ctor.item v := rfl

example : (.empty : Prog .pure (Parcel Int32)) = Parcel.Obj.Ctor.empty := rfl

example : (do
    let p : Val (Parcel Int32) ← Parcel.empty
    return p : Prog .pure (Parcel Int32)) = (do
    let p ← (Parcel.Obj.Ctor.empty : Prog .pure (Parcel Int32))
    return p : Prog .pure (Parcel Int32)) := rfl

example (v : Val Int32 .persistent) :
    (.some v : Prog .pure MaybeI32) = MaybeI32.Obj.Ctor.some v := rfl

example (v : Val Int32) : (.some v : Prog .pure (Option Int32)) = Oria.Option.some v := rfl

-- Ordinary host expressions and local name resolution retain Lean's meaning.
example : (MaybeI32.some 3 : MaybeI32) = .some 3 := rfl

example : (do
    let rock := Choice.Obj.Ctor.paper
    let c ← rock
    return c : Prog .pure Choice) = (do
    let c ← Choice.Obj.Ctor.paper
    return c : Prog .pure Choice) := rfl

example : (do
    let c := Choice.rock
    match c with
    | .rock => .paper
    | _ => .scissors : Prog .pure Choice) = Choice.Obj.Ctor.paper := rfl

namespace IntegerAction
def action (v : Val Int32) : Prog .pure Int32 := Prog.pure v
end IntegerAction

namespace BooleanAction
def action (v : Val Bool) : Prog .pure Bool := Prog.pure v
end BooleanAction

open IntegerAction BooleanAction in
example (v : Val Int32) : (action v : Prog .pure Int32) = Prog.pure v := rfl

example : (do
    let n : Val Int32 ← Std.Scoreboard.get .self "points"
    return n : Prog (Std.Scoreboard.readGrade .self) Int32) = (do
    let n ← Std.Scoreboard.get .self "points"
    return n : Prog (Std.Scoreboard.readGrade .self) Int32) := rfl

/-- error: a leading-dot object constructor needs a datatype -/
#guard_msgs(error, substring := true) in
example : Prog .pure Choice := do
  let c ← .rock
  return c

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example : Prog .pure Choice .persistent := .rock

/-- error: Application type mismatch -/
#guard_msgs(error, substring := true) in
example (v : Val Bool) : Prog .pure MaybeI32 := .some v

/-- error: an object constructor must be fully applied -/
#guard_msgs(error, substring := true) in
example : Prog .pure MaybeI32 := MaybeI32.some

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example : Prog .pure Choice := (Choice.rock : Choice)

@[mcfunction]
private def shorthand (v : Val Int32) : Prog .pure MaybeI32 := .some v

@[mcfunction]
private def explicit (v : Val Int32) : Prog .pure MaybeI32 := MaybeI32.Obj.Ctor.some v

run_cmd
  let short ← Oria.Proofs.McFunctionUtil.elaborate ``shorthand
  let full ← Oria.Proofs.McFunctionUtil.elaborate ``explicit
  unless short.definition.pretty 100 == full.definition.pretty 100 do
    throwError "constructor spellings produced different Trees"

end Oria.Proofs.Constructors
