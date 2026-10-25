module

public import Oria.Command.Execute
public import Oria.IR.Common.Operator
public import Oria.IR.Common.Reference
public import Oria.IR.Common.Memory
public import Oria.IR.Common.Scope

namespace Oria.IR.Cont

/-- Typed atomic values whose local case is exact membership in `Γ`. -/
public inductive Atom (Γ : List ObjTy) : ObjTy → Type where
  | local {a : ObjTy} : Scope.Var Unit Γ a → Atom Γ a
  | unit : Atom Γ .unit
  | bool : Bool → Atom Γ .bool
  | i32 : Int32 → Atom Γ .i32
  deriving DecidableEq

namespace Atom

/-- Rename every local through a total type-preserving context map. -/
@[expose] public def rename {Γ : List ObjTy} {a : ObjTy} {Δ : List ObjTy}
    (value : Atom Γ a)
    (ρ : Scope.Renaming Unit Unit Γ Δ) : Atom Δ a :=
  match value with
  | .local x => .local (ρ x)
  | .unit => .unit
  | .bool value => .bool value
  | .i32 value => .i32 value

/-- Shift an atom beneath one fresh binder. -/
@[expose] public def weaken {Γ : List ObjTy} {a : ObjTy} (value : Atom Γ a) (b : ObjTy) : Atom (b :: Γ) a :=
  value.rename ((Scope.Renaming.id Unit Γ).weaken b)

/-- Shift an atom beneath a fresh binder telescope. -/
@[expose] public def weakenMany {Γ : List ObjTy} {a : ObjTy} (value : Atom Γ a) :
    (bs : List ObjTy) → Atom (bs ++ Γ) a
  | bs => value.rename ⟨fun x => x.weakenMany bs⟩

@[simp] public theorem rename_id {Γ : List ObjTy} {a : ObjTy} (value : Atom Γ a) :
    value.rename (Scope.Renaming.id Unit Γ) = value := by
  cases value <;> rfl

@[simp] public theorem rename_comp {Γ : List ObjTy} {a : ObjTy} {Δ : List ObjTy} {Ε : List ObjTy}
    (value : Atom Γ a)
    (ρ : Scope.Renaming Unit Unit Γ Δ)
    (σ : Scope.Renaming Unit Unit Δ Ε) :
    (value.rename ρ).rename σ = value.rename (σ.comp ρ) := by
  cases value <;> rfl

end Atom

/-- Typed primitive operations whose arguments and command holes all inhabit `Γ`. -/
public inductive Op (Γ : List ObjTy) : Grade → ObjTy → Type where
  | division : Atom Γ .i32 → Atom Γ .i32 → Op Γ .failure .i32
  | checkpoint : (forced : Bool) → Op Γ .suspension .unit
  | copy {a : ObjTy} : Atom Γ a → Op Γ .pure a
  | unary {a b : ObjTy} : UnaryOp a b → Atom Γ a → Op Γ .pure b
  | binary {a b c : ObjTy} : BinaryOp a b c → Atom Γ a → Atom Γ b → Op Γ .pure c
  | construct {a : ObjTy} {fields : List ObjTy} :
      Constructor a fields → Args (Atom Γ) fields → Op Γ .pure a
  | call {sig : Signature} : DeclRef sig → Args (Atom Γ) sig.args → Op Γ sig.grade sig.result
  | execute {params : List ObjTy} {g : Grade} : (scope : Execute.Scope (Atom Γ)) →
      DeclRef ⟨params, .i32, g⟩ → Args (Atom Γ) params →
      Op Γ (scope.grade g) .unit
  | memory {g : Grade} {fields : List ObjTy} {a : ObjTy} :
      MemoryOp g fields a → Args (Atom Γ) fields → Op Γ g a
  | command {route : Command.Signature} :
      (request : Command.Call (Atom Γ) route) →
      Op Γ request.grade .i32

namespace Op

/-- Map every operand, including dynamic command holes, through a typed atomic substitution. -/
@[expose] public def map {Γ : List ObjTy} {g : Grade} {a : ObjTy} {Δ : List ObjTy}
    (operation : Op Γ g a)
    (f : ∀ {a}, Atom Γ a → Atom Δ a) : Op Δ g a :=
  match operation with
  | .division left right => .division (f left) (f right)
  | .checkpoint forced => .checkpoint forced
  | .copy value => .copy (f value)
  | .unary operator value => .unary operator (f value)
  | .binary operator left right => .binary operator (f left) (f right)
  | .construct constructor arguments => .construct constructor (arguments.map f)
  | .call reference arguments => .call reference (arguments.map f)
  | .execute scope reference arguments => .execute (scope.map f) reference (arguments.map f)
  | .memory operation arguments => .memory operation (arguments.map f)
  | .command request => request.map_grade f ▸ .command (request.map f)

@[simp] private theorem map_cast {g : Grade} {h' : Grade} {Γ : List ObjTy} {a : ObjTy} {Δ : List ObjTy}
    (h : g = h') (op : Op Γ g a)
    (f : ∀ {a}, Atom Γ a → Atom Δ a) :
    (h ▸ op).map f = h ▸ (op.map f) := by cases h; rfl

@[simp] private theorem map_command {Γ : List ObjTy} {sig : Command.Signature} {Δ : List ObjTy}
    (request : Command.Call (Atom Γ) sig)
    (f : ∀ {a}, Atom Γ a → Atom Δ a) :
    (Op.command request).map f = request.map_grade f ▸ Op.command (request.map f) := rfl

private theorem command_heq {Γ : List ObjTy} {sig : Command.Signature}
    {x y : Command.Call (Atom Γ) sig} (h : x = y) :
    HEq (Op.command x) (Op.command y) := by cases h; rfl

private theorem execute_heq {Γ : List ObjTy} {params : List ObjTy} {g : Grade}
    {x y : Execute.Scope (Atom Γ)}
    (ref : DeclRef ⟨params, .i32, g⟩)
    (as bs : Args (Atom Γ) params) (h : x = y) (same : as = bs) :
    HEq (Op.execute x ref as) (Op.execute y ref bs) := by
  cases h
  cases same
  rfl

/-- Rename every operand through a total scope map. -/
@[expose] public def rename {Γ : List ObjTy} {g : Grade} {a : ObjTy} {Δ : List ObjTy}
    (operation : Op Γ g a)
    (ρ : Scope.Renaming Unit Unit Γ Δ) : Op Δ g a :=
  operation.map (fun value => value.rename ρ)

@[simp] public theorem rename_id {Γ : List ObjTy} {g : Grade} {a : ObjTy} (operation : Op Γ g a) :
    operation.rename (Scope.Renaming.id Unit Γ) = operation := by
  cases operation with
  | division left right => simp [rename, map]
  | checkpoint forced => simp [rename, map]
  | copy value => simp [rename, map]
  | unary operator value => simp [rename, map]
  | binary operator left right => simp [rename, map]
  | construct constructor arguments => simp [rename, map]
  | call reference arguments => simp [rename, map]
  | execute scope reference arguments =>
      have same : (fun {a} (value : Atom Γ a) => value.rename (.id Unit Γ)) =
          (fun {_a} value => value) := by
        funext a value
        exact Atom.rename_id value
      apply eq_of_heq
      apply execute_heq reference
      · simpa only [same] using Execute.Scope.map_id scope
      · simp only [same, Args.map_id]
  | memory operation arguments => simp [rename, map]
  | command request =>
      simp only [rename, map]
      have same :
          (fun {type} (value : Atom Γ type) =>
            value.rename (Scope.Renaming.id Unit Γ)) =
            (fun {_type} value => value) := by
        funext type value
        exact Atom.rename_id value
      apply eq_of_heq
      refine (eqRec_heq (φ := fun g => Op Γ g .i32) _ _).trans (command_heq ?_)
      simpa only [same] using Command.Call.map_id request

@[simp] public theorem rename_comp {Γ : List ObjTy} {g : Grade} {a : ObjTy}
    {Δ : List ObjTy} {Ε : List ObjTy}
    (operation : Op Γ g a)
    (ρ : Scope.Renaming Unit Unit Γ Δ)
    (σ : Scope.Renaming Unit Unit Δ Ε) :
    (operation.rename ρ).rename σ = operation.rename (σ.comp ρ) := by
  cases operation with
  | division left right => simp [rename, map]
  | checkpoint forced => simp [rename, map]
  | copy value => simp [rename, map]
  | unary operator value => simp [rename, map]
  | binary operator left right => simp [rename, map]
  | construct constructor arguments => simp [rename, map, Args.map_comp]
  | call reference arguments => simp [rename, map, Args.map_comp]
  | execute scope reference arguments =>
      have same : (fun {a} (value : Atom Γ a) => (value.rename ρ).rename σ) =
          (fun {a} value => value.rename (σ.comp ρ)) := by
        funext a value
        exact Atom.rename_comp value ρ σ
      apply eq_of_heq
      apply execute_heq reference
      · simp only [Execute.Scope.map_comp, same]
      · simp only [Args.map_comp, same]
  | memory operation arguments => simp [rename, map, Args.map_comp]
  | command request =>
      simp only [rename, map_command, map_cast]
      have same :
          (fun {type} (value : Atom Γ type) =>
            (value.rename ρ).rename σ) =
            (fun {type} value => value.rename (σ.comp ρ)) := by
        funext type value
        exact Atom.rename_comp value ρ σ
      apply eq_of_heq
      refine (eqRec_heq (φ := fun g => Op Ε g .i32) _ _).trans <|
        (eqRec_heq (φ := fun g => Op Ε g .i32) _ _).trans <|
        (command_heq ?_).trans (eqRec_heq (φ := fun g => Op Ε g .i32) _ _).symm
      rw [Command.Call.map_comp, same]

end Op

mutual
  /-- Scoped ANF with explicit multi-argument joins and one-level constructor tests. -/
  public inductive Comp : List ObjTy → ObjTy → List (List ObjTy) → Type where
    | fail {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} : Comp Γ result joins
    | invoke {Γ : List ObjTy} {g : Grade} {a result : ObjTy} {joins : List (List ObjTy)} :
        Op Γ g a → Comp (a :: Γ) result joins → Comp Γ result joins → Comp Γ result joins
    | ret {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
        Atom Γ result → Comp Γ result joins
    | letOp {Γ : List ObjTy} {g : Grade} {a : ObjTy} {result : ObjTy}
        {joins : List (List ObjTy)} :
        Op Γ g a → Comp (a :: Γ) result joins → Comp Γ result joins
    | branch {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
        Atom Γ .bool → Comp Γ result joins → Comp Γ result joins →
        Comp Γ result joins
    | switch {Γ : List ObjTy} {a : ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
        Atom Γ a → Arms Γ a result joins → Comp Γ result joins
    | letJoin {params : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
        {Γ : List ObjTy} :
        Comp params result joins → Comp Γ result (params :: joins) →
        Comp Γ result joins
    | jump {joins : List (List ObjTy)} {params : List ObjTy} {Γ : List ObjTy}
        {result : ObjTy} :
        Scope.Var Unit joins params → Args (Atom Γ) params → Comp Γ result joins

  /-- Payload variables enter scope only along the corresponding constructor edge. -/
  public inductive Arms : List ObjTy → ObjTy → ObjTy → List (List ObjTy) → Type where
    | nil {Γ : List ObjTy} {a : ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
        Arms Γ a result joins
    | default {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} {a : ObjTy} :
        Comp Γ result joins → Arms Γ a result joins
    | cons {a : ObjTy} {fields : List ObjTy} {Γ : List ObjTy} {result : ObjTy}
        {joins : List (List ObjTy)} :
        Constructor a fields → Comp (fields ++ Γ) result joins →
        Arms Γ a result joins → Arms Γ a result joins
end

end Oria.IR.Cont
