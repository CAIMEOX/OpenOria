module

public import Oria
import Oria.Datapack
import Oria.Proofs.BackendUtil
meta import Oria
meta import Oria.Datapack
meta import Oria.Proofs.BackendUtil

namespace Oria.Proofs.Payload

open Oria Oria.Std Oria.Datapack

public inductive Chain (A : Type) where
  | nil
  | cons (head : A) (tail : Chain A)
  deriving Oria.Object

public structure Pair where
  left : Int32
  right : Option Int32
  deriving Oria.Object

@[mcfunction]
def first (xs : Val (Chain Int32)) : Prog .pure Int32 := do
  match xs with
  | .nil => return 0
  | .cons x _ => return x

@[mcfunction]
def total (p : Val Pair) : Prog .pure Int32 := do
  match p with
  | .mk x (.some y) => return x + y
  | .mk x .none => return x

@[mcfunction]
def readPlus : Prog (Scoreboard.readGrade .self) Int32 := do
  let x ← Scoreboard.get .self (.ofString "points")
  return x + 1

@[mcfunction]
def materialized : Prog (Scoreboard.readGrade .self).handled (Option Int32) :=
  Prog.attempt readPlus.call

@[mcfunction]
def run : Prog (Grade.handled (Scoreboard.writeGrade .self)) Unit := do
  let tail ← Chain.Obj.Ctor.nil (A := Int32)
  let xs ← Chain.Obj.Ctor.cons (7 : Val Int32) tail
  let x ← first.call xs
  let y ← Oria.Option.some (2 : Val Int32)
  let p ← Pair.Obj.Ctor.mk x y
  let result ← total.call p
  (Scoreboard.set .self (.ofString "points") (.dynamic result)).ignore

@[datapack]
def specimen : Spec := build { ns := .ofString "payload" } do
  entry (.ofString "run") run.ref

#guard specimen.artifact.files.any fun file =>
  file.path.toString == "data/payload/function/run.mcfunction"

namespace Mutual

mutual
  public inductive Tree (A : Type) where
    | leaf (value : A)
    | node (children : Forest A)

  public inductive Forest (A : Type) where
    | nil
    | cons (first : Tree A) (rest : Forest A)
end

deriving instance Oria.Object for Tree, Forest

end Mutual

@[mcfunction]
def mutualI32 (_ : Val (Mutual.Tree Int32)) : Prog (Grade.handled .pure) Unit := Prog.pure Val.unit

@[mcfunction]
def mutualBool (_ : Val (Mutual.Tree Bool)) : Prog (Grade.handled .pure) Unit := Prog.pure Val.unit

@[mcfunction]
def mixedGrade (tree : Val (Mutual.Tree Int32)) : Prog (Scoreboard.readGrade .self) Int32 := do
  match tree with
  | .leaf value => return value
  | .node _ => Scoreboard.get .self (.ofString "points")

run_cmd
  let ⟨source, _⟩ ← Oria.Proofs.BackendUtil.compile
    #[⟨_, mutualI32.ref⟩, ⟨_, mutualBool.ref⟩, ⟨_, mixedGrade.ref⟩]
  unless source.collected.candidate.schemas.size == 4 do
    throwError "mutual generic instances did not retain four distinct closed schemas"

end Oria.Proofs.Payload
