module

public import Oria.Language.Builder
import all Oria.Language.Builder
import all Oria.Data.Sealed

namespace Oria.Persistent

open Oria.IR

/-- A named persistent cell and its closed initializer, both fixed while constructing the program. -/
public structure Root (A : Type) {a : ObjTy} [Object A a] where
  private mk ::
  private representation : Sealed A (RootRef a × McFunction.Internal.Recipe)

private def Root.ref {A : Type} {a : ObjTy} [Object A a] (root : Root A) : RootRef a :=
  root.representation.get.1

set_option backward.privateInPublic true in
private opaque Root.initializer {A : Type} {a : ObjTy} [Object A a]
    (root : Root A) : McFunction.Internal.Recipe := root.representation.get.2

/-- Copy an eligible object graph into the persistent arena, retaining its sharing. -/
public def persist {A : Type} {a : ObjTy} [Object A a]
    (value : Val A) : Prog allocGrade A .persistent :=
  private_decl% perform (.memory .persist (.cons (reveal value) .nil))

namespace Root

public def init {A : Type} {a : ObjTy} [Object A a] {g : Grade}
    (initial : Prog g A .persistent) (name : Lean.Name := by exact decl_name%) : Root A :=
  private_decl% ⟨Sealed.mk (⟨name⟩, McFunction.Internal.capture (name ++ `initial) initial)⟩

public def get {A : Type} {a : ObjTy} [Object A a]
    (root : Root A) : Prog readGrade A .persistent :=
  private_decl% perform (.memory (.rootGet root.ref) .nil)

public def set {A : Type} {a : ObjTy} [Object A a]
    (root : Root A) (value : Val A .persistent) : Prog writeGrade Unit :=
  private_decl% perform (.memory (.rootSet root.ref) (.cons (reveal value) .nil))

end Root

namespace Ref

public def new {A : Type} {a : ObjTy} [Object A a]
    (value : Val A .persistent) : Prog allocGrade (Ref A) .persistent :=
  private_decl% perform (.memory .refNew (.cons (reveal value) .nil))

public def get {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (cell : Val (Ref A) r) : Prog readGrade A .persistent :=
  private_decl% perform (.memory .refGet (.cons (reveal cell) .nil))

public def set {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (cell : Val (Ref A) r) (value : Val A .persistent) : Prog writeGrade Unit :=
  private_decl% perform (.memory .refSet (.cons (reveal cell) (.cons (reveal value) .nil)))

end Ref

end Oria.Persistent
