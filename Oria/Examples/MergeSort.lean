module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# NBT merge sort

The input is a native list of I32 values at `merge_sort:state input`. Calling the exported
sort function submits a cooperative task; successful completion publishes output while
preserving input. Two typed arena lists hold successive merge passes. Dynamic indices enter
function macros, and scalar heads remain in the register/stack calling convention.
-/

namespace Oria.Examples.MergeSort

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def state : DataTarget := .storage "merge_sort:state"

private structure Buffers where
  values : Array (Array Int32)
  deriving Nbt.Repr

private def buffer (b : Val Int32) := Buffers.Nbt.values.at b
private def item (b i : Val Int32) := (buffer b).at i

/-- Native storage operations with cooperative suspension and failure propagation. -/
@[expose] public def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure ||| Eff.suspend |||
    Eff.memoryRead ||| Eff.memoryWrite⟩

private def push (s : Val (Nbt.Ref Buffers)) (dst v : Val Int32) :=
  Nbt.append s (buffer dst) (.i32 v)

@[mcfunction]
private def importInput (s : Val (Nbt.Ref Buffers)) (input : Val Nbt.Data) (n : Val Int32) :
    Prog grade Unit := do
  let rec again (i : Val Int32) : Prog grade Unit := do
    if i >= n then return Val.unit
    else
      Task.checkpoint
      let x ← Nbt.numberAt input ⟨.index i, []⟩
      push s 0 x
      again (i + 1)
  again 0

@[mcfunction]
private def drain (s : Val (Nbt.Ref Buffers)) (src dst lo hi : Val Int32) : Prog grade Unit := do
  let rec again (i : Val Int32) : Prog grade Unit := do
    if i >= hi then return Val.unit
    else
      Task.checkpoint
      Nbt.appendFrom s (buffer dst) s (item src i)
      again (i + 1)
  again lo

@[mcfunction]
private def mergeRange (s : Val (Nbt.Ref Buffers)) (src dst lo mid hi : Val Int32) : Prog grade Unit := do
  if mid == hi then drain.call s src dst lo mid
  else
    let x ← s.values[src][lo]
    let y ← s.values[src][mid]
    let rec again (i j x y : Val Int32) : Prog grade Unit := do
      Task.checkpoint
      if x <= y then
        push s dst x
        if i + 1 < mid then
          let next ← s.values[src][i + 1]
          again (i + 1) j next y
        else drain.call s src dst j hi
      else
        push s dst y
        if j + 1 < hi then
          let next ← s.values[src][j + 1]
          again i (j + 1) x next
        else drain.call s src dst i mid
    again lo mid x y

/-- Clip an interval endpoint using the remaining length, keeping additions in range. -/
@[mcfunction]
private def limit (lo width n : Val Int32) : Prog .pure Int32 := do
  if width < n - lo then return lo + width else return n

@[mcfunction]
private def pass (s : Val (Nbt.Ref Buffers)) (src dst start width n : Val Int32) : Prog grade Unit := do
  let rec again (lo : Val Int32) : Prog grade Unit := do
    if lo >= n then return Val.unit
    else
      Task.checkpoint
      let mid ← limit.call lo width n
      let hi ← limit.call mid width n
      mergeRange.call s src dst lo mid hi
      again hi
  again start

@[mcfunction]
private def rounds (s : Val (Nbt.Ref Buffers)) (first second initial n : Val Int32) : Prog grade Int32 := do
  let rec again (src dst width : Val Int32) : Prog grade Int32 := do
    if width >= n then return src
    else
      Task.checkpoint
      (Nbt.clear s (buffer dst)).ignore
      pass.call s src dst 0 width n
      let next ← limit.call width width n
      again dst src next
  again first second initial

/-- Snapshot the input, copy numeric elements into typed I32 buffers, sort in bounded
slices, and publish the result. Input and prior output are preserved until publication.
Completion, failure, and cancellation release the task arena. -/
@[mcfunction]
public def sort : Prog grade Unit := do
  let input ← Data.readOne state (some (.key "input"))
  let n ← Nbt.measure input
  let s ← Nbt.alloc (Buffers.mk #[#[], #[]])
  importInput.call s input n
  let result ← rounds.call s 0 1 1 n
  (Nbt.store s (buffer result) state (.key "output")).ignore

/-- Cooperative sorting pack with 128 registers and a 2048-command slice budget. -/
@[datapack]
public def specimen : Spec := build {ns := "merge_sort", sliceBudget := 2048} do
  task "sort" sort.ref

/-- The same sorting program with stack-resident ordinary words. -/
@[datapack]
public def stacked : Spec := build {ns := "merge_sort_stack", registerBudget := 6, sliceBudget := 2048} do
  task "sort" sort.ref

end Oria.Examples.MergeSort
