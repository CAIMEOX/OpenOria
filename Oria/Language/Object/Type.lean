module

public import Oria.IR.Common.Type

namespace Oria

namespace Persistent

/-- Source marker for a persistent mutable cell; object values are created by Ref operations. -/
public inductive Ref (A : Type) where
  | token

end Persistent

/-- The source-to-object correspondence is issued by the deriving implementation. -/
public def Object.Evidence (_A : Type) (_code : ObjTy) : Prop := True

/-- Canonical correspondence between a Lean source type and its logical object code.
Instances retain an abstract witness issued by the deriving implementation. -/
public class Object (A : Type) (code : outParam ObjTy) : Prop where
  private mk ::
  private evidence : Object.Evidence A code

set_option backward.privateInPublic true in
private theorem makeObject {A : Type} {code : ObjTy} : Object A code :=
  ⟨True.intro⟩

public instance : Object Unit .unit := makeObject

public instance : Object Bool .bool := makeObject

public instance : Object Int32 .i32 := makeObject

public instance {t : Option Nbt.Tag} : Object (Nbt.Data t) (.nbt t) := makeObject

public instance {a : Type} [r : Nbt.Repr a] : Object (Nbt.Ref a) (.nbtRef r.schema) := makeObject

public instance {A : Type} {code : ObjTy} [Object A code] : Object (Option A) (.option code) := makeObject


public instance {A : Type} {code : ObjTy} [Object A code] : Object (Persistent.Ref A) (.ref code) := makeObject

end Oria
