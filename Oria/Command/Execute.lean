module

public import Oria.Command.Selector
public import Oria.Effect.Context

namespace Oria.Execute

universe u u'

open Oria.Command

/-- Store receivers determine the effect of delivering a native command result. -/
public inductive StoreKind where
  | score | nbt | bossbar
  deriving BEq, DecidableEq, Repr

/-- The native operation determines context supply; its argument retains its own reads. -/
public inductive Kind where
  | asEntity | atEntity | positioned | positionedAs | rotated | rotatedAs
  | inDimension | anchored | align | facing | facingEntity
  | onEntity | summon | positionedOver
  | ifCondition | unlessCondition
  | storeResult : StoreKind → Kind
  | storeSuccess : StoreKind → Kind
  deriving BEq, DecidableEq, Repr

namespace Kind

@[expose] public def tokens : Kind → List SyntaxToken
  | .asEntity => ["as"]
  | .atEntity => ["at"]
  | .positioned => ["positioned"]
  | .positionedAs => ["positioned", "as"]
  | .rotated => ["rotated"]
  | .rotatedAs => ["rotated", "as"]
  | .inDimension => ["in"]
  | .anchored => ["anchored"]
  | .align => ["align"]
  | .facing => ["facing"]
  | .facingEntity => ["facing", "entity"]
  | .ifCondition => ["if"]
  | .unlessCondition => ["unless"]
  | .onEntity => ["on"]
  | .summon => ["summon"]
  | .positionedOver => ["positioned", "over"]
  | .storeResult _ => ["store", "result"]
  | .storeSuccess _ => ["store", "success"]

@[expose] public def change : Kind → ContextChange
  | .asEntity => ⟨Req.none, Req.executor⟩
  | .atEntity => ⟨Req.none, Req.position ||| Req.rotation ||| Req.dimension⟩
  | .positioned => ⟨Req.none, Req.position ||| Req.anchor⟩
  | .positionedAs => ⟨Req.none, Req.position⟩
  | .rotated | .rotatedAs => ⟨Req.none, Req.rotation⟩
  | .inDimension => ⟨Req.position ||| Req.dimension, Req.dimension⟩
  | .anchored => ⟨Req.none, Req.anchor⟩
  | .align => ⟨Req.position, Req.none⟩
  | .facing | .facingEntity => ⟨Req.position ||| Req.anchor ||| Req.executor, Req.rotation⟩
  | .onEntity => ⟨Req.executor, Req.executor⟩
  | .summon => ⟨Req.position ||| Req.dimension, Req.executor⟩
  | .positionedOver => ⟨Req.position ||| Req.dimension, Req.position⟩
  | .ifCondition | .unlessCondition | .storeResult _ | .storeSuccess _ => .id

@[expose] public def effects : Kind → EffRow
  | .storeResult .score | .storeSuccess .score => Eff.world ||| Eff.scoreboardWrite
  | .storeResult .nbt | .storeSuccess .nbt => Eff.world
  | .storeResult .bossbar | .storeSuccess .bossbar => Eff.world ||| Eff.hud
  | .summon => Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.hud ||| Eff.sound
  | _ => Eff.world ||| Eff.scoreboardRead ||| Eff.random

@[expose] public def capturesSuccess : Kind → Bool
  | .storeResult _ | .storeSuccess _ => true
  | _ => false

@[expose] public def capturesResult : Kind → Bool
  | .storeResult _ => true
  | _ => false

end Kind

public structure Step (v : ObjTy → Type) where
  kind : Kind
  argument : Fragment v

namespace Step

/-- Supply an executor for each matching entity, retaining position, rotation, dimension, and anchor. -/
@[expose] public def «as» {v : ObjTy → Type} (selector : Selector) : Step v := ⟨.asEntity, selector.fragment⟩
/-- Supply position, rotation, and dimension for each matching entity, retaining executor and anchor. -/
@[expose] public def «at» {v : ObjTy → Type} (selector : Selector) : Step v := ⟨.atEntity, selector.fragment⟩

@[expose] public def change {v : ObjTy → Type} (step : Step v) : ContextChange :=
  ⟨step.kind.change.need ||| step.argument.requirements, step.kind.change.give⟩

@[expose] public def fragment {v : ObjTy → Type} (step : Step v) : Fragment v :=
  .spaced ((step.kind.tokens.map Fragment.token) ++ [step.argument])

end Step

/-- A compiled execution prefix, with its context transformation preserved across IR maps. -/
public structure Scope (v : ObjTy → Type) where
  fragment : Fragment v
  change : ContextChange
  effects : EffRow
  captureSuccess : Bool
  captureResult : Bool

namespace Scope

@[expose] public def ofSteps {v : ObjTy → Type} (steps : List (Step v)) : Scope v :=
  let change := steps.foldl (fun (c : ContextChange) step => c.seq step.change) ContextChange.id
  let fragment := Fragment.spaced (.token "execute" :: steps.map Step.fragment)
  Scope.mk { fragment with requirements := change.need } change
    (steps.foldl (fun e step => e ||| step.kind.effects) Eff.none)
    (steps.any (fun step => step.kind.capturesSuccess))
    (steps.any (fun step => step.kind.capturesResult))

@[expose] public def grade {v : ObjTy → Type} (scope : Scope v) (body : Grade) : Grade :=
  ⟨scope.change.apply body.req, scope.effects ||| body.handled.eff⟩

@[expose] public def map {v w : ObjTy → Type} (f : ∀ {a}, v a → w a) (scope : Scope v) : Scope w :=
  Scope.mk (scope.fragment.map f) scope.change scope.effects scope.captureSuccess scope.captureResult

public def traverseK {v w : ObjTy → Type} {r : Type u}
    (visit : ∀ {a}, v a → (w a → r) → r)
    (scope : Scope v) (next : Scope w → r) : r :=
  scope.fragment.traverseK visit fun fragment =>
    next ⟨fragment, scope.change, scope.effects, scope.captureSuccess, scope.captureResult⟩

@[expose] public def AllT {v : ObjTy → Type} (p : ∀ {a}, v a → Type u) (scope : Scope v) :=
  scope.fragment.AllT p

public def traverseKAllT {v : ObjTy → Type} {p : ∀ {a}, v a → Type u} {w : ObjTy → Type}
    {r : Type u'}
    (visit : ∀ {a} (value : v a), p value → (w a → r) → r)
    (scope : Scope v) (evidence : scope.AllT p) (next : Scope w → r) : r :=
  scope.fragment.traverseKAllT visit evidence fun fragment =>
    next ⟨fragment, scope.change, scope.effects, scope.captureSuccess, scope.captureResult⟩

@[simp] public theorem map_grade {v w : ObjTy → Type}
    (f : ∀ {a}, v a → w a) (scope : Scope v) (g : Grade) :
    (scope.map f).grade g = scope.grade g := rfl

@[simp] public theorem map_id {v : ObjTy → Type} (scope : Scope v) : scope.map (fun x => x) = scope := by
  cases scope
  simp [map, Fragment.map_id]

public theorem map_comp {v w z : ObjTy → Type}
    (f : ∀ {a}, v a → w a) (g : ∀ {a}, w a → z a) (scope : Scope v) :
    (scope.map f).map g = scope.map (fun x => g (f x)) := by
  cases scope
  simp [map, Fragment.map_comp]

end Scope

end Oria.Execute
