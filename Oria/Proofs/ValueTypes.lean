module

public import Oria.Proofs.Fixtures.ValueTypes
import Oria.IR.Representation.Persistent
meta import Oria.Proofs.Fixtures.ValueTypes
meta import Oria.IR.Representation.Persistent

namespace Oria.Proofs.ValueTypes

open Oria Oria.Representation Oria.Proofs.Fixtures.ValueTypes

@[value_type]
public structure Scalar (A : Type) where
  value : A
  deriving Oria.Object

public inductive Color where
  | red | blue
  deriving Oria.Object

#guard (Table.build #[Scalar.Oria.schema (A := Int32)]).isOk
#guard (Table.build #[Color.Oria.schema, Scalar.Oria.schema (A := Color)]).isOk
#guard match Table.build #[Scalar.Oria.schema (A := Option Int32)] with
  | .error (.pointerValueField _ _) => true
  | _ => false

/-- error: `value_type` requires exactly one constructor -/
#guard_msgs(error, substring := true) in
@[value_type]
public inductive Invalid where
  | first | second

private def layouts := Table.build #[Empty.Oria.schema, Word.Oria.schema, Triple.Oria.schema,
  Quad.Oria.schema, Box.Oria.schema]

#guard match layouts with
  | .ok table => table.width Empty.Oria.code == 0 && table.width Word.Oria.code == 1 &&
      table.width Triple.Oria.code == 3 && table.width Quad.Oria.code == 4 &&
      table.width Box.Oria.code == 1 &&
      (table.kinds Quad.Oria.code).toList == List.replicate 4 .scalar
  | _ => false

private def a : TypeId := ⟨`Fixture.A, []⟩
private def b : TypeId := ⟨`Fixture.B, []⟩

#guard match Table.build #[⟨a, [⟨`Fixture.A.mk, [.data a]⟩], .value⟩] with
  | .error (.recursiveValueType _) => true
  | _ => false

#guard match Table.build #[⟨a, [⟨`Fixture.A.mk, [.data b]⟩], .value⟩,
    ⟨b, [⟨`Fixture.B.mk, [.data a]⟩], .value⟩] with
  | .error (.recursiveValueType _) => true
  | _ => false

#guard ([ObjTy.option .i32, .ref .i32, .nbt none]).all fun field =>
  match Table.build #[⟨a, [⟨`Fixture.A.mk, [field]⟩], .value⟩] with
  | .error (.pointerValueField _ _) => true
  | _ => false

#guard match Table.build #[⟨a, [⟨`Fixture.A.mk, [.data b]⟩], .value⟩,
    ⟨b, [⟨`Fixture.B.mk, [.i32]⟩], .ordinary⟩] with
  | .error (.pointerValueField _ _) => true
  | _ => false

private def wide (n : Nat) := Table.build #[
  ⟨a, [⟨`Fixture.A.mk, List.replicate n .i32⟩], .value⟩,
  ⟨b, [⟨`Fixture.B.mk, [.data a]⟩], .ordinary⟩]

#guard (wide 31 >>= fun table => Persistent.build table #[.data a]).isOk
#guard match wide 31 >>= (fun table => Persistent.build table #[.data b]) with
  | .error (.persistentLayoutTooWide _ 31) => true
  | _ => false
#guard match wide 31 >>= (fun table => Persistent.build table #[.ref (.data a)]) with
  | .error (.persistentLayoutTooWide _ 31) => true
  | _ => false
#guard (wide 30 >>= fun table => Persistent.build table #[.data b, .ref (.data a)]).isOk

end Oria.Proofs.ValueTypes
