module

public import Oria.IR.Cont.Definition

namespace Oria.IR.Cont

open Oria.IR

/-- A finite usage mask over the exact lexical context `Γ`. -/
public abbrev Support (Γ : List ObjTy) := Fin Γ.length → Bool

namespace Support

@[expose] public def empty {Γ : List ObjTy} : Support Γ :=
  fun _ => false

@[expose] public def singleton {Γ : List ObjTy} {a : ObjTy} (x : Scope.Var Unit Γ a) : Support Γ :=
  fun i => decide (i = x.index)

@[expose] public def combine {Γ : List ObjTy} (left right : Support Γ) : Support Γ :=
  fun i => left i || right i

/-- Remove the newest binder and re-index the remaining lexical positions. -/
@[expose] public def dropHead {a : ObjTy} {Γ : List ObjTy} (support : Support (a :: Γ)) : Support Γ :=
  fun i => support i.succ

/-- Remove a telescope of newest binders and re-index the ambient positions. -/
@[expose] public def dropMany {as : List ObjTy} {Γ : List ObjTy} (support : Support (as ++ Γ)) : Support Γ :=
  fun i => support ⟨i.val + as.length, by
    simp only [List.length_append]
    omega⟩

@[expose] public def Contains {Γ : List ObjTy} {a : ObjTy}
    (support : Support Γ) (x : Scope.Var Unit Γ a) : Prop :=
  support x.index = true

@[expose] public def Included {Γ : List ObjTy} (left right : Support Γ) : Prop :=
  ∀ i, left i = true → right i = true

public instance {Γ : List ObjTy} {a : ObjTy}
    (support : Support Γ) (x : Scope.Var Unit Γ a) :
    Decidable (support.Contains x) := by
  unfold Contains
  infer_instance

@[simp] public theorem not_contains_empty {Γ : List ObjTy} {a : ObjTy} (x : Scope.Var Unit Γ a) :
    ¬empty.Contains x := by
  simp [empty, Contains]

@[simp] public theorem contains_singleton {Γ : List ObjTy} {a : ObjTy} (x : Scope.Var Unit Γ a) :
    (singleton x).Contains x := by
  simp [singleton, Contains]

@[simp] public theorem contains_combine {Γ : List ObjTy} {a : ObjTy} {left right : Support Γ}
    (x : Scope.Var Unit Γ a) :
    (combine left right).Contains x ↔ left.Contains x ∨ right.Contains x := by
  simp [combine, Contains, Bool.or_eq_true]

@[simp] public theorem contains_dropHead {b : ObjTy} {Γ : List ObjTy} {a : ObjTy}
    (support : Support (b :: Γ)) (x : Scope.Var Unit Γ a) :
    (dropHead support).Contains x ↔ support.Contains (x.weaken b) := by
  change support x.index.succ = true ↔ support (x.weaken b).index = true
  rw [show (x.weaken b).index = x.index.succ by
    apply Fin.ext
    simp]

@[simp] public theorem contains_dropMany {as : List ObjTy} {Γ : List ObjTy} {a : ObjTy}
    (support : Support (as ++ Γ)) (x : Scope.Var Unit Γ a) :
    (dropMany support).Contains x ↔ support.Contains (x.weakenMany as) := by
  change support ⟨x.index.val + as.length, _⟩ = true ↔
    support (x.weakenMany as).index = true
  rw [show (x.weakenMany as).index = ⟨x.index.val + as.length, by
      simp only [List.length_append]
      omega⟩ by
    apply Fin.ext
    simp]

public theorem contains_of_included {Γ : List ObjTy} {left right : Support Γ} {a : ObjTy}
    {x : Scope.Var Unit Γ a}
    (included : Included left right)
    (present : left.Contains x) : right.Contains x :=
  included x.index present

end Support

namespace Atom

@[expose] public def support {Γ : List ObjTy} {a : ObjTy} : Atom Γ a → Support Γ
  | .local x => .singleton x
  | .unit | .bool _ | .i32 _ => .empty

end Atom

@[expose] public def supportArgs {Γ : List ObjTy} {types : List ObjTy} : Args (Atom Γ) types → Support Γ
  | .nil => .empty
  | .cons value rest => value.support.combine (supportArgs rest)

@[expose] public def supportRequest {Γ : List ObjTy} {route : Command.Signature}
    (request : Command.Call (Atom Γ) route) : Support Γ :=
  request.traverseK
    (fun value next => value.support.combine (next value))
    (fun _ => .empty)

namespace Op

@[expose] public def support {Γ : List ObjTy} {g : Grade} {a : ObjTy} : Op Γ g a → Support Γ
  | .copy value => value.support
  | .unary _ value => value.support
  | .binary _ left right | .division left right => left.support.combine right.support
  | .construct _ arguments => supportArgs arguments
  | .call _ arguments => supportArgs arguments
  | .checkpoint _ => .empty
  | .memory _ arguments => supportArgs arguments
  | .command request => supportRequest request
  | .execute scope _ arguments =>
      scope.traverseK (fun value next => value.support.combine (next value))
        (fun _ => supportArgs arguments)

end Op

mutual
  @[expose] public def Comp.support {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
      Comp Γ result joins → Support Γ
    | .fail => .empty
    | .invoke operation next failed =>
        operation.support.combine ((Support.dropHead next.support).combine failed.support)
    | .ret value => value.support
    | .letOp operation next =>
        operation.support.combine (Support.dropHead next.support)
    | .branch condition yes no =>
        condition.support.combine (yes.support.combine no.support)
    | .switch value arms => value.support.combine arms.support
    | .letJoin _ next => next.support
    | .jump _ values => supportArgs values

  @[expose] public def Arms.support {Γ : List ObjTy} {a : ObjTy} {result : ObjTy}
      {joins : List (List ObjTy)} : Arms Γ a result joins → Support Γ
    | .nil => .empty
    | .default body => body.support
    | .cons (fields := fields) _ body rest =>
        (Support.dropMany (as := fields) body.support).combine rest.support
end

namespace Comp

@[expose] public def Uses {Γ : List ObjTy} {r : ObjTy} {joins : List (List ObjTy)} {a : ObjTy}
    (computation : Comp Γ r joins) (x : Scope.Var Unit Γ a) : Prop :=
  computation.support.Contains x

@[expose] public def Unused {Γ : List ObjTy} {r : ObjTy} {joins : List (List ObjTy)} {a : ObjTy}
    (computation : Comp Γ r joins) (x : Scope.Var Unit Γ a) : Prop :=
  ¬computation.Uses x

public instance {Γ : List ObjTy} {r : ObjTy} {joins : List (List ObjTy)} {a : ObjTy}
    (computation : Comp Γ r joins) (x : Scope.Var Unit Γ a) :
    Decidable (computation.Uses x) := by
  unfold Uses Support.Contains
  infer_instance

public instance {Γ : List ObjTy} {r : ObjTy} {joins : List (List ObjTy)} {a : ObjTy}
    (computation : Comp Γ r joins) (x : Scope.Var Unit Γ a) :
    Decidable (computation.Unused x) := by
  unfold Unused
  infer_instance

@[simp] public theorem support_ret {Γ : List ObjTy} {r : ObjTy} {joins : List (List ObjTy)}
    (value : Atom Γ r) :
    (Comp.ret (joins := joins) value).support = value.support := rfl

@[simp] public theorem support_jump {joins : List (List ObjTy)} {params Γ : List ObjTy} {r : ObjTy}
    (join : Scope.Var Unit joins params)
    (arguments : Args (Atom Γ) params) :
    (Comp.jump (result := r) join arguments).support = supportArgs arguments := rfl

@[simp] public theorem support_letJoin {params : List ObjTy} {r : ObjTy} {joins : List (List ObjTy)}
    {Γ : List ObjTy}
    (body : Comp params r joins)
    (next : Comp Γ r (params :: joins)) :
    (Comp.letJoin body next).support = next.support := rfl

end Comp
end Oria.IR.Cont
