module

public meta import Oria.Meta.McFunction
public meta import Oria.Meta.ObjectDerive
import Oria.Language.Builder
import Oria.Meta.Elab.ProgMatch

namespace Oria.Proofs.Region

open Oria

@[mcfunction]
def keep {r : Oria.Region} (v : Val Int32 r) : Prog .pure Int32 r :=
  Prog.bind (Prog.pure v) (fun x => Prog.pure x)

example (v : Val Int32 .persistent) : Val Int32 := v

example (v : Val Int32 .persistent) : Prog .pure Int32 .persistent :=
  keep.call v

example (v : Val Int32) : Prog .pure Int32 := keep.call v

example : keep.signature = ⟨[.i32], .i32, .pure⟩ := rfl

public inductive Tree where
  | tip
  | fork (left right : Tree)
  deriving Oria.Object

@[mcfunction]
def left {r : Oria.Region} (v : Val Tree r) : Prog .pure Tree r := do
  let tree ← Prog.pure v
  match tree with
  | .tip => return tree
  | .fork child _ => return child

example (v : Val Tree .persistent) : Prog .pure Tree .persistent := left.call v

@[mcfunction]
def readOnly (v : Val Int32 .persistent) : Prog .failure Int32 := do
  let next := v + 1
  let a ← v / 5
  let b ← 6 / v
  let mixed := (2 + v) * (v - 3) + (4 - v) * a + b * (7 * v) + (v * 8)
  return next + mixed

example : (let x := 1; let y := x + 2; y) = (3 : Nat) := rfl

@[mcfunction]
def choose {r : Oria.Region} (c : Val Bool r) (x y : Val Tree r) : Prog .pure Tree r := do
  if c then return x else return y

@[mcfunction]
def annotated (v : Val Int32 .persistent) : Prog .pure Int32 := do
  let x : Val Int32 ← Prog.pure v
  return x

end Oria.Proofs.Region
