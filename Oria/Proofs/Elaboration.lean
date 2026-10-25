module

public import Oria.Examples.Elaboration
meta import Oria
meta import Oria.Examples.Elaboration

namespace Oria.Proofs.Elaboration

open Oria Oria.Examples.Elaboration

example (n : Val Int32) :
    (do
      let x := n + 10
      return x * x : Prog .pure Int32) =
    (do
      let x ← Prog.pure (n + 10)
      return x * x : Prog .pure Int32) := rfl

example {A : Type} {a : ObjTy} [Object A a] {r : Region} (value : Val A r) :
    (do let x := value; return x : Prog .pure A r) =
      Prog.bind (Prog.pure value) (fun x => Prog.pure x) := rfl

example (s : Val State) :
    (do
      return {s with counters.wins := 10, counters.losses := 20}
      : Prog .pure State) =
    (do
      let result ← (Prog.pure s).bind fun _outer =>
        ((Prog.pure _outer.counters).bind fun _ =>
          (show Prog .pure Counters from Counters.mk 10 20)).bind fun c =>
            (show Prog .pure State from State.mk c _outer.rounds)
      return result : Prog .pure State) := rfl

example : Prog .pure State := do
  return {counters.wins := 10, counters.losses := 20, rounds := 30}

example {g : Grade} (p : Prog g Int32) :
    (do let _action := p; return Val.unit : Prog .pure Unit) = Prog.pure Val.unit := rfl

example (n : Val Int32) :
    (do let amount : Nat := 3; return n + amount : Prog .pure Int32) =
      Prog.pure (n + 3) := rfl

example (n : Val Int32) :
    (do
      let rec go (i : Val Int32) : Prog .pure Int32 := do
        if i <= 0 then return 0
        go (i - 1)
      go n : Prog .pure Int32) =
    Prog.fix (fun (go : Val Int32 → Prog .pure Int32) i => do
      if i <= 0 then return 0
      go (i - 1)) n := rfl

example (value : Val (Option Int32)) : Prog .pure Int32 := do
  let .some x := value | return 0
  return x

example (n : Val Int32) : Prog .pure Int32 := do
  let rec go : Val Int32 → Prog .pure Int32 := fun i => do
    if i <= 0 then return 0
    go (i - 1)
  go n

example (n : Val Int32) : Prog .pure Int32 := do
  let rec generated (i : Nat) : Prog .pure Int32 := do
    match i with
    | 0 => return n
    | i + 1 => generated i
  generated 3

example : Prog .pure Int32 := do
  let values := []
  let values : List Nat := values
  return I32.lit (Int32.ofNat values.length)

public structure Child extends Counters where
  rounds : Int32
  deriving Oria.Object

example (s : Val Child) : Prog .pure Child := do
  return {s with toCounters.wins := s.toCounters.wins + 1}

example (s : Val Child) (c : Val Counters) : Prog .pure Child := do
  return {s with toCounters := c}

public structure NativeBase where
  count : Int32
  deriving Nbt.Repr

public structure NativeChild extends NativeBase where
  title : String
  deriving Nbt.Repr

example (s : Val (Nbt.Ref NativeChild)) := show Prog _ Int32 from do
  let n ← s.count
  s.count := n + 1
  let n ← s.count
  return n

example (s : Val (Nbt.Ref NativeChild)) : Prog IR.Nbt.writeGrade Unit := do
  s.count := 1

example (s : Val (Nbt.Ref Buffer)) := show Prog _ Unit from do
  s.values[0] := #[1, 2, 3]
  s := Buffer.mk #[#[4, 5]] "whole"

example (s : Val (Nbt.Ref (Array Int32))) (b : Val Bool) (n : Val Int32) :
    (do
      if b then s[0] := n
      return Val.unit : Prog IR.Nbt.writeGrade Unit) =
    (do
      if b then Nbt.set s (Nbt.Access.root.at (0 : Val Int32)) (.i32 n)
      return Val.unit : Prog IR.Nbt.writeGrade Unit) := rfl

example (s : Val (Nbt.Ref (Array Int32))) (b : Bool) (n : Val Int32) :
    (do
      if b then s[0] := n
      return Val.unit : Prog IR.Nbt.writeGrade Unit) =
    (do
      if b then Nbt.set s (Nbt.Access.root.at (0 : Val Int32)) (.i32 n)
      return Val.unit : Prog IR.Nbt.writeGrade Unit) := rfl

example (s : Val (Nbt.Ref (Array Int32))) (k n : Val Int32) :
    (do
      match k with
      | 0 => s[0] := n
      | _ => s[1] := n
      return Val.unit : Prog IR.Nbt.writeGrade Unit) =
    (do
      match k with
      | 0 => Nbt.set s (Nbt.Access.root.at (0 : Val Int32)) (.i32 n)
      | _ => Nbt.set s (Nbt.Access.root.at (1 : Val Int32)) (.i32 n)
      return Val.unit : Prog IR.Nbt.writeGrade Unit) := rfl

example (s : Val (Nbt.Ref (Array Int32))) (b : Val Bool) :
    (do
      if b then
        let n := Id.run do
          let mut n := 0
          if true then n := n + 1
          return n
        s[0] := n
      return Val.unit : Prog IR.Nbt.writeGrade Unit) =
    (do
      if b then s[0] := 1
      return Val.unit : Prog IR.Nbt.writeGrade Unit) := rfl

example (s : Val (Nbt.Ref (Array Int32))) (n : Val Int32) :
    (do
      for i in ([0, 1] : List Nat) do
        s[i] := n
      : Prog IR.Nbt.writeGrade Unit) =
    (do
      for i in ([0, 1] : List Nat) do
        Nbt.set s (Nbt.Access.root.at (I32.lit (Int32.ofNat i))) (.i32 n)
      : Prog IR.Nbt.writeGrade Unit) := rfl

/-- error: typed NBT indexing requires an Array field -/
#guard_msgs(error, substring := true) in
example (s : Val (Nbt.Ref Buffer)) (b : Val Bool) : Prog IR.Nbt.writeGrade Unit := do
  if b then s.label[0] := 1
  return Val.unit

/-- error: field `counters` has already been specified -/
#guard_msgs(error, substring := true) in
example (s : Val State) : Prog .pure State := do
  return {s with counters := s.counters, counters.wins := 2}

/-- error: nested object updates require a derived record field -/
#guard_msgs(error, substring := true) in
example (s : Val State) : Prog .pure State := do
  return {s with rounds.count := 2}

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example (s : Val State .persistent) : Prog .pure State .persistent := do
  return {s with counters.wins := 2}

/-- error: NBT selection binds I32 values -/
#guard_msgs(error, substring := true) in
example (s : Val (Nbt.Ref Buffer)) : Prog IR.Nbt.readGrade Int32 := do
  let x ← s.label
  return x

/-- error: typed NBT indexing requires an Array field -/
#guard_msgs(error, substring := true) in
example (s : Val (Nbt.Ref Buffer)) : Prog IR.Nbt.readGrade Int32 := do
  let x ← s.label[0]
  return x

/-- error: unknown NBT field -/
#guard_msgs(error, substring := true) in
example (s : Val (Nbt.Ref Buffer)) : Prog IR.Nbt.readGrade Int32 := do
  let x ← s.absent
  return x

/-- error: a runtime recursive function requires explicit parameter, result, and grade annotations -/
#guard_msgs(error, substring := true) in
example (n : Val Int32) : Prog .pure Int32 := do
  let rec go (i : Val Int32) : Prog _ Int32 := do
    if i <= 0 then return 0
    go (i - 1)
  go n

/-- error: an Oria runtime `let rec` binds one function -/
#guard_msgs(error, substring := true) in
example (n : Val Int32) : Prog .pure Int32 := do
  let rec a (i : Val Int32) : Prog .pure Int32 := Prog.pure i,
    b (i : Val Int32) : Prog .pure Int32 := Prog.pure i
  a n

end Oria.Proofs.Elaboration
