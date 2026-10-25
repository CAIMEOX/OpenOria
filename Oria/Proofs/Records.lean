module

public import Oria
meta import Oria

namespace Oria.Proofs.Records

open Oria

public structure Box (A : Type) where
  item : A
  count : Int32
  deriving Oria.Object

public structure Nested where
  box : Box Int32
  flag : Bool
  deriving Oria.Object

example {A : Type} {a : ObjTy} [Object A a] {r : Region} (v : Val (Box A) r) : Val A r :=
  v.item

example {r : Region} (v : Val Nested r) : Val Int32 r := v.box.item

@[mcfunction]
private def count {r : Region} (v : Val (Box Int32) r) : Prog .pure Int32 :=
  Prog.pure (v.item + v.count)

@[mcfunction]
private def updated {r : Region} (v : Val (Box Int32) r) : Prog .pure (Box Int32) := do
  return {v with count := v.count + 1}

@[mcfunction]
private def constructed (n : Val Int32) : Prog .pure (Box Int32) := do
  return {item := n, count := 0}

example (v : Val (Box Int32) .persistent) : Prog .pure (Box Int32) := updated.call v

/-- error: Type mismatch -/
#guard_msgs(error, substring := true) in
example (v : Val (Box Int32) .persistent) : Prog .pure (Box Int32) .persistent := do
  return {v with count := 0}

/-- error: missing object record field `count` -/
#guard_msgs(error, substring := true) in
example : Prog .pure (Box Int32) := do
  return {item := 1}

/-- error: unknown field -/
#guard_msgs(error, substring := true) in
example (v : Val (Box Int32)) : Prog .pure (Box Int32) := do
  return {v with absent := 1}

example : Box Int32 := {item := 1, count := 2}
example (v : Box Int32) : Box Int32 := {v with count := v.count + 1}

end Oria.Proofs.Records
