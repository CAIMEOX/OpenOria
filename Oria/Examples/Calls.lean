module

public import Oria
public meta import Oria

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Function calls

These programs retain object values across named calls. Ordinary Lean helpers assemble the
programs during construction; every `.call` retains a first-order function boundary.
-/

namespace Oria.Examples.Calls

open Oria

/-- The leaf of the arithmetic call chains. -/
@[mcfunction]
public def leaf (n : Val Int32) : Prog .pure Int32 := return n + 1

private def carry (next : Val Int32 → Prog .pure Int32) (n : Val Int32) : Prog .pure Int32 := do
  let old := n + 3
  let value ← next (n + 1)
  return old + value

/-- Retain one value across a leaf call. -/
@[mcfunction]
public def chain1 (n : Val Int32) : Prog .pure Int32 := carry leaf.call n

/-- Two nested callers retaining their own values. -/
@[mcfunction]
public def chain2 (n : Val Int32) : Prog .pure Int32 := carry chain1.call n

/-- Four named functions, with three values retained at different call depths. -/
@[mcfunction]
public def chain3 (n : Val Int32) : Prog .pure Int32 := carry chain2.call n

/-- Extend the chain with a fifth named function. -/
@[mcfunction]
public def chain4 (n : Val Int32) : Prog .pure Int32 := carry chain3.call n

/-- Six named functions sharing the same host generator. -/
@[mcfunction]
public def chain5 (n : Val Int32) : Prog .pure Int32 := carry chain4.call n

/-- Seven named functions retaining values at successive depths. -/
@[mcfunction]
public def chain6 (n : Val Int32) : Prog .pure Int32 := carry chain5.call n

/-- Eight named functions. At input 4 the returned value is 82. -/
@[mcfunction]
public def chain7 (n : Val Int32) : Prog .pure Int32 := carry chain6.call n

/-- The left branch retains a product while calling the shared arithmetic chain. -/
@[mcfunction]
public def left (n : Val Int32) : Prog .pure Int32 := do
  let old := n * 2
  let value ← chain2.call (n + 1)
  return old + value

/-- The right branch reaches the same chain through a shorter path. -/
@[mcfunction]
public def right (n : Val Int32) : Prog .pure Int32 := do
  let old := n * 3
  let value ← chain1.call (n + 2)
  return old + value

/-- A branching call graph with shared callees and values live across multiple calls.
At input 4 the returned value is 149. -/
@[mcfunction]
public def tree (n : Val Int32) : Prog .pure Int32 := do
  let old := n + 10
  let l ← left.call n
  let r ← right.call (n + 1)
  let value ← leaf.call (l + r)
  return old + l + r + value

/-- Runtime alternatives select two branches whose callees share a leaf. -/
@[mcfunction]
public def choose (n : Val Int32) : Prog .pure Int32 := do
  let old := n + 10
  if n < 0 then
    let value ← left.call (-n)
    return old + value
  else
    let value ← right.call n
    return old + value

/-- Twenty-four demanded parameters share the regular register/stack calling convention. -/
@[mcfunction]
public def sum24 (a b c d e f g h i j k l m n o p q r s t u v w x : Val Int32) : Prog .pure Int32 :=
  return a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s + t + u + v + w + x

/-- Sixteen distinct values stay live across a 24-argument call and a branching call graph.
At input 4 the returned value is 9061. -/
@[mcfunction]
public def locals (n : Val Int32) : Prog .pure Int32 := do
  let x1 := n + 1
  let x2 := n + 2
  let x3 := n + 3
  let x4 := n + 4
  let x5 := n + 5
  let x6 := n + 6
  let x7 := n + 7
  let x8 := n + 8
  let x9 := n + 9
  let x10 := n + 10
  let x11 := n + 11
  let x12 := n + 12
  let x13 := n + 13
  let x14 := n + 14
  let x15 := n + 15
  let x16 := n + 16
  let first ← sum24.call (n + 1) (n + 2) (n + 3) (n + 4) (n + 5) (n + 6)
    (n + 7) (n + 8) (n + 9) (n + 10) (n + 11) (n + 12) (n + 13) (n + 14)
    (n + 15) (n + 16) (n + 17) (n + 18) (n + 19) (n + 20) (n + 21) (n + 22) (n + 23) (n + 24)
  let second ← tree.call (n + first)
  return first + second + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 +
    x12 + x13 + x14 + x15 + x16

end Oria.Examples.Calls
