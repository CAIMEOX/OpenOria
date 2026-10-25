module

public import Oria
meta import Oria

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Type-directed elaboration

These definitions exercise host lets, shared object values, nested record updates,
local recursion, and typed native paths. The source rules and their return/effect
contracts are collected in `docs/elaboration.md`.
-/

namespace Oria.Examples.Elaboration

open Oria

/-- Two counters represented as an object record. -/
public structure Counters where
  /-- Successful operations. -/
  wins : Int32
  /-- Failed operations. -/
  losses : Int32
  deriving Oria.Object

/-- A nested object record. -/
public structure State where
  /-- Counters updated through a common field prefix. -/
  counters : Counters
  /-- Number of updates. -/
  rounds : Int32
  deriving Oria.Object

/-- A native document whose fields include both numeric and host-only data. -/
public structure Buffer where
  /-- Numeric rows addressed with runtime indices. -/
  values : Array (Array Int32)
  /-- A native string written from a host value. -/
  label : String
  deriving Nbt.Repr

/-- The shared expression is bound before its two uses. The host constant stays at
construction time, and naming an action does not execute it. -/
@[mcfunction]
public def shared (n : Val Int32) : Prog .pure Int32 := do
  let offset : Nat := 10
  let x := n + offset
  let action := Prog.pure x
  let y ← action
  return x * y

/-- Rebuild the counters once while retaining the source record's contents. -/
@[mcfunction]
public def update {r : Region} (s : Val State r) : Prog .pure State := do
  return {s with
    counters.wins := s.counters.wins + 1
    counters.losses := s.counters.losses + 2
    rounds := s.rounds + 1}

/-- An exhaustive pure-value pattern uses the object pattern compiler. -/
@[mcfunction]
public def total (s : Val State) : Prog .pure Int32 := do
  let .mk (.mk w l) rounds := s
  return w * 100 + l * 10 + rounds

/-- Non-tail local recursion produces first-order object calls. -/
@[mcfunction]
public def fib (n : Val Int32) : Prog .pure Int32 := do
  let rec go (i : Val Int32) : Prog .pure Int32 := do
    if i <= 1 then return i
    let a ← go (i - 1)
    let b ← go (i - 2)
    return a + b
  go n

/-- A local tail-recursive function captures an object value from its lexical scope. -/
@[mcfunction]
public def sum (n offset : Val Int32) : Prog .pure Int32 := do
  let base := offset + 1
  let rec go (i acc : Val Int32) : Prog .pure Int32 := do
    if i <= 0 then return acc + base
    go (i - 1) (acc + i)
  go n 0

/-- A Nat-parameter recursion runs in the host language during construction. -/
@[mcfunction]
public def hostRecursion (n : Val Int32) : Prog .pure Int32 := do
  let rec count (n : Nat) : Nat := match n with | 0 => 0 | n + 1 => count n + 1
  return n + count 3

/-- Read and replace one typed numeric selection, then write a native string.
Missing indices use Failure. The label write ignores its native result so an already
edited document can be updated again. The string remains native data. -/
@[mcfunction]
public def edit (s : Val (Nbt.Ref Buffer)) (i j : Val Int32) := show Prog _ Int32 from do
  let x ← s.values[i][j]
  s.values[i][j] := x + 1
  (Nbt.set s Buffer.Nbt.label (.literal "edited")).ignore
  let y ← s.values[i][j]
  return y

end Oria.Examples.Elaboration
