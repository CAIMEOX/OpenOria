module

import Oria.IR.Representation.Persistent
meta import Oria.IR.Representation.Persistent

namespace Oria.Proofs.PersistentLayout

open Oria Oria.IR Oria.Representation

private def color : TypeId := ⟨`Fixture.Color, []⟩

private def colorTable : Except Diagnostic Table :=
  Table.build #[
    ⟨color, [
      ⟨`Fixture.Color.red, []⟩,
      ⟨`Fixture.Color.blue, []⟩
    ], .ordinary⟩
  ]

private def pair : TypeId := ⟨`Fixture.Pair, []⟩

private def pairTable : Except Diagnostic Table :=
  Table.build #[
    ⟨pair, [⟨`Fixture.Pair.mk, [.i32, .option .i32]⟩], .ordinary⟩
  ]

private def link : TypeId := ⟨`Fixture.Link, []⟩

private def linkTable : Except Diagnostic Table :=
  Table.build #[
    ⟨link, [
      ⟨`Fixture.Link.end, []⟩,
      ⟨`Fixture.Link.next, [.i32, .ref (.data link)]⟩
    ], .ordinary⟩
  ]

private def sharedA : TypeId := ⟨`Fixture.SharedA, []⟩
private def sharedB : TypeId := ⟨`Fixture.SharedB, []⟩

private def sharedTable : Except Diagnostic Table :=
  Table.build #[
    ⟨sharedA, [⟨`Fixture.SharedA.mk, [.i32]⟩], .ordinary⟩,
    ⟨sharedB, [⟨`Fixture.SharedB.mk, [.bool]⟩], .ordinary⟩
  ]

private def wide : TypeId := ⟨`Fixture.Wide, []⟩

private def wideTable (slots : Nat) : Except Diagnostic Table :=
  Table.build #[⟨wide, [⟨`Fixture.Wide.mk, List.replicate slots .i32⟩], .ordinary⟩]

private def containsRetain {n slots : Nat} (actions : Vector (Persistent.Action n) slots) : Bool :=
  actions.toList.any fun action =>
    match action with
    | .retainRef _ => true
    | _ => false

example :
    (colorTable >>= fun table => Persistent.build table #[.data color]).toOption.map (fun plans =>
      match plans.lookup? (.data color) with
      | some index => match plans.nodes[index] with
        | .immediate _ => true
        | _ => false
      | none => false) = some true := by
  native_decide

example :
    (pairTable >>= fun table => Persistent.build table #[.option .i32]).toOption.map (fun plans =>
      match plans.lookup? (.option .i32) with
      | some index => match plans.nodes[index] with
        | .boxed _ constructors => constructors.map (fun constructor =>
            constructor.layout.scanCode) == #[1, 2]
        | _ => false
      | none => false) = some true := by
  native_decide

example :
    (linkTable >>= fun table => Persistent.build table #[.ref (.data link)]).toOption.map (fun plans =>
      match plans.lookup? (.ref (.data link)) with
      | some index => match plans.nodes[index] with
        | .ref _ _ layout =>
            layout.constructor == `Oria.Persistent.Ref &&
              layout.payload.toList == [.pointer (.data link)]
        | _ => false
      | none => false) = some true := by
  native_decide

example :
    (linkTable >>= fun table => Persistent.build table #[.ref (.data link)]).toOption.map (fun plans =>
      match (plans.lookup? (.data link)).map (plans.nodes.get ·) with
      | some (.boxed _ constructors) =>
          constructors.any fun constructor => containsRetain constructor.actions
      | _ => false) = some true := by
  native_decide

example :
    (sharedTable >>= fun table => Persistent.build table #[.data sharedA, .data sharedB]).toOption.map
      (fun plans => plans.scanners.size == 1) = some true := by
  native_decide

example :
    (sharedTable >>= fun table => Persistent.build table #[.data sharedA, .data sharedA]).toOption.map
      (fun plans => plans.nodeCount == 2) = some true := by
  native_decide

example :
    (wideTable 30 >>= fun table => Persistent.build table #[.data wide]).isOk = true := by
  native_decide

example :
    (match wideTable 31 >>= (fun table => Persistent.build table #[.data wide]) with
    | .error diagnostic => diagnostic == .persistentLayoutTooWide (.data wide) 31
    | .ok _ => false) = true := by
  native_decide


end Oria.Proofs.PersistentLayout
