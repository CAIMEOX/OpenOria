module

public meta import Oria.Meta.Persistent
public meta import Oria.Meta.ObjectDerive
import Oria.Language.Persistent
import Oria.Meta.Elab.ProgMatch
import Oria.Datapack.Spec
meta import Oria.Datapack.Spec
import Oria.Meta.Datapack
meta import Oria.Meta.Datapack
import Oria.Proofs.Fixtures.PersistentRoot
meta import Oria.Proofs.Fixtures.PersistentRoot

namespace Oria.Proofs.Persistent

open Oria Oria.Persistent

@[root]
def points : Root Int32 := Root.init (persist 0)

@[mcfunction]
def increment : Prog stateGrade Unit := do
  let old ← points
  let next ← persist (old + 1)
  points := next

@[mcfunction]
def alias : Prog stateGrade Unit := do
  let cell := points
  let old ← cell
  let next ← persist (old + 1)
  cell := next

@[mcfunction]
def imported : Prog stateGrade Unit := do
  let old ← Fixtures.PersistentRoot.points
  let next ← persist (old + 1)
  Fixtures.PersistentRoot.points := next

@[mcfunction]
def assignBranch (condition : Val Bool) : Prog (allocGrade.seq writeGrade) Unit := do
  let one ← persist 1
  let two ← persist 2
  if condition then
    points := one
  else
    points := two

public inductive Link where
  | end
  | next (value : Int32) (tail : Ref Link)
  deriving Oria.Object

@[root]
def list : Root (Ref Link) := Root.init do
  let last ← Link.Obj.Ctor.end
  let last ← persist last
  Ref.new last

@[mcfunction]
def prepend : Prog stateGrade Unit := do
  let tail ← list
  let node ← Link.Obj.Ctor.next 1 tail
  let node ← persist node
  let head ← Ref.new node
  list := head

private def spec : Datapack.Spec :=
  Datapack.build { ns := .ofString "memory" } do
    Datapack.root (.ofString "memory:points") points
    Datapack.root (.ofString "memory:list") list
    Datapack.entry (.ofString "increment") increment.ref
    Datapack.entry (.ofString "prepend") prepend.ref
    Datapack.collector (.ofString "gc")

#guard spec.persistentRoots.size == 2
#guard spec.collectors.size == 1
#guard spec.roots.size == 2
#guard spec.check.isOk

@[datapack]
private def game : Datapack.Spec := spec

public inductive Wide where
  | mk (a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1 c1 d1 e1 : Int32)
  deriving Oria.Object

/--
error: Oria.Diagnostic.persistentLayoutTooWide
-/
#guard_msgs(error, substring := true) in
@[mcfunction]
def oversized (v : Val Wide) : Prog allocGrade Wide .persistent := persist v


end Oria.Proofs.Persistent
