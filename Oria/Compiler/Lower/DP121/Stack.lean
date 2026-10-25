module

public import Oria.Compiler.Lower.DP121.Layout
public import Oria.Compiler.Lower.DP121.Transfer
public import Oria.Compiler.RegAlloc.Location
import Oria.Nbt.Syntax

namespace Oria.Lower.DP121

open Oria.Target.DP121

/-- A scalar location after register and frame assignment. -/
public inductive Place where
  | score : Score → Place
  | storage : StoragePath → Place
  deriving BEq, DecidableEq, Repr

namespace Stack

public inductive Frame where
  | current
  | caller
  deriving BEq, DecidableEq, Repr

public inductive Part where
  | locals
  | saved
  | result
  deriving BEq, DecidableEq, Repr

public structure Shape where
  locals : Nat := 0
  saved : Nat := 0
  result : Nat := 0

public def Shape.needed (shape : Shape) : Bool :=
  shape.locals != 0 || shape.saved != 0 || shape.result != 0

private def path (storage : ResourceId) (key : String) : StoragePath :=
  ⟨storage, .key key⟩

public def slot (storage : ResourceId) (frame : Frame) (part : Part) (index : Nat) : StoragePath :=
  let depth : Int := match frame with | .current => -1 | .caller => -2
  let key := match part with | .locals => "locals" | .saved => "saved" | .result => "result"
  ⟨storage, ⟨.key ⟨"stack"⟩, [.index depth, .key ⟨key⟩, .index index]⟩⟩

public def place {k slots : Nat} (bank : Layout k) (storage : ResourceId) (frame : Frame) :
    RegAlloc.Loc k slots → Place
  | .reg r => .score bank.registers[r]
  | .stack s => .storage (slot storage frame .locals s.val)

/-- All copies address one exact scalar leaf. -/
public def move (copy : Transfer.Move Place) : Command .plain :=
  match copy.target, copy.source with
  | .score target, .imm value => .scoreboard (.set target value)
  | .score target, .loc (.score source) => .scoreboard (.operation target .assign source)
  | .score target, .loc (.storage source) => .store .result (.score target) (.data (.get source))
  | .storage target, .imm value => .data (.setValue target (.int value))
  | .storage target, .loc (.score source) =>
      .store .result (.storageI32 target) (.scoreboard (.get source))
  | .storage target, .loc (.storage source) => .data (.setFrom target source)

public def parallel {k : Nat} (bank : Layout k) (copies : List (Transfer.Move Place)) :
    Except Diagnostic (List (Command .plain)) := do
  let some sequence := Transfer.schedule (.score bank.scratch[0]) copies
    | throw Diagnostic.invalidParallelTransfer
  pure (sequence.code.map move)

public def begin (storage : ResourceId) : List (Command .plain) :=
  [.data (.setValue (path storage "stack") (nbt% []))]

public def finish (storage : ResourceId) : List (Command .plain) :=
  [.data (.remove (path storage "stack"))]

public def push (storage : ResourceId) (shape : Shape) : List (Command .plain) :=
  let words (n : Nat) := Array.replicate n (0 : Int32)
  let value := nbt% {
    locals: $(words shape.locals), saved: $(words shape.saved), result: $(words shape.result)}
  [.data (.setValue (path storage "stack_draft") value),
    .data (.appendFrom (path storage "stack") (path storage "stack_draft")),
    .data (.remove (path storage "stack_draft"))]

public def pop (storage : ResourceId) : List (Command .plain) :=
  [.data (.remove (⟨storage, ⟨.key ⟨"stack"⟩, [.index (-1)]⟩⟩ : StoragePath))]

end Stack
end Oria.Lower.DP121
