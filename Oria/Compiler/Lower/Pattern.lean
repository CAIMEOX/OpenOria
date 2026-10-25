module

public import Oria.IR.Cont.Definition
public import Oria.IR.Catalog.Object
import Std.Data.HashSet.Lemmas

namespace Oria.Lower.Pattern

open Oria.IR
open Oria.IR.Cont

/-- A residual source row and its typed transfer to the already-compiled RHS. -/
public structure Row (Γ types : List ObjTy) (joins : List (List ObjTy)) where
  index : Nat
  {bindings params : List ObjTy}
  patterns : Tree.Patterns types bindings
  target : Scope.Var Unit joins params
  arguments : ∀ {Δ}, Scope.Renaming Unit Unit Γ Δ →
    Args (Atom Δ) bindings → Args (Atom Δ) params

namespace Row

public def rename {Γ types : List ObjTy} {joins : List (List ObjTy)} {Δ : List ObjTy}
    (row : Row Γ types joins) (ρ : Scope.Renaming Unit Unit Γ Δ) :
    Row Δ types joins :=
  { row with arguments := fun σ values => row.arguments (σ.comp ρ) values }

public def weakenJoin {Γ types : List ObjTy} {joins : List (List ObjTy)}
    (row : Row Γ types joins) (params : List ObjTy) :
    Row Γ types (params :: joins) :=
  { row with target := row.target.weaken params }

end Row

mutual
  private def bindings? {a : ObjTy} {bindings : List ObjTy} {Γ : List ObjTy}
      (pattern : Tree.Pattern a bindings) (value : Atom Γ a) :
      Option (Args (Atom Γ) bindings) :=
    match pattern with
    | .any => some .nil
    | .bind => some (.cons value .nil)
    | .ctor _ _ | .i32 _ => none

  private def allBindings? {types bindings Γ : List ObjTy}
      (patterns : Tree.Patterns types bindings)
      (values : Args (Atom Γ) types) : Option (Args (Atom Γ) bindings) :=
    match patterns, values with
    | .nil, .nil => some .nil
    | .cons head rest, .cons value values => do
        let head ← bindings? head value
        let rest ← allBindings? rest values
        pure (head.append rest)
end

/-- The default matrix drops rows testing the selected column. -/
private def defaultRow {Γ : List ObjTy} {a : ObjTy} {types : List ObjTy}
    {joins : List (List ObjTy)}
    (value : Atom Γ a) (row : Row Γ (a :: types) joins) :
    Option (Row Γ types joins) :=
  match a, row with
  | _, @Row.mk _ _ _ index _ _ (.cons .any rest) target arguments =>
      some ⟨index, rest, target, arguments⟩
  | _, @Row.mk _ _ _ index _ _ (.cons .bind rest) target arguments =>
      some ⟨index, rest, target,
        fun ρ values => arguments ρ (.cons (value.rename ρ) values)⟩
  | _, @Row.mk _ _ _ _ _ _ (.cons (.ctor _ _) _) _ _ => none
  | .i32, @Row.mk _ _ _ _ _ _ (.cons (.i32 _) _) _ _ => none

/-- Specialization exposes a constructor's fields inside its guarded successor. -/
private def specialize {a : ObjTy} {fields Γ types : List ObjTy} {joins : List (List ObjTy)}
    (constructor : Constructor a fields) (value : Atom Γ a)
    (row : Row Γ (a :: types) joins) : Option (Row (fields ++ Γ) (fields ++ types) joins) :=
  let ρ := Scope.Renaming.appendRight Unit fields Γ
  match a, row with
  | _, @Row.mk _ _ _ index _ _ (.cons .any rest) target arguments =>
      some ⟨index, (Tree.Patterns.ignoreAll fields).append rest, target,
        fun σ values => arguments (σ.comp ρ) values⟩
  | _, @Row.mk _ _ _ index _ _ (.cons .bind rest) target arguments =>
      some ⟨index, (Tree.Patterns.ignoreAll fields).append rest, target,
        fun σ values => arguments (σ.comp ρ) (.cons (value.rename (σ.comp ρ)) values)⟩
  | _, @Row.mk _ _ _ index _ _ (.cons (.ctor (fields := other) candidate inner) rest) target arguments =>
      if shape : other = fields then
        if candidate.name == constructor.name then
          some ⟨index, (shape ▸ inner).append rest, target,
            fun σ values => arguments (σ.comp ρ) values⟩
        else none
      else none
  | .i32, @Row.mk _ _ _ _ _ _ (.cons (.i32 _) _) _ _ => none

private def headConstructor? {Γ : List ObjTy} {a : ObjTy} {types : List ObjTy}
    {joins : List (List ObjTy)}
    (row : Row Γ (a :: types) joins) :
    Option ((fields : List ObjTy) × Constructor a fields) :=
  match a, row with
  | _, @Row.mk _ _ _ _ _ _ (.cons (.ctor constructor _) _) _ _ => some ⟨_, constructor⟩
  | _, @Row.mk _ _ _ _ _ _ (.cons .any _) _ _ | _, @Row.mk _ _ _ _ _ _ (.cons .bind _) _ _ => none
  | .i32, @Row.mk _ _ _ _ _ _ (.cons (.i32 _) _) _ _ => none

private def headI32? {Γ types : List ObjTy} {joins : List (List ObjTy)}
    (row : Row Γ (.i32 :: types) joins) : Option Int32 :=
  match row with
  | @Row.mk _ _ _ _ _ _ (.cons (.i32 value) _) _ _ => some value
  | _ => none

/-- Integer constants specialize like nullary constructors. Wildcards retain their order
and a bound variable receives the original discriminant. -/
private def specializeI32 {Γ types : List ObjTy} {joins : List (List ObjTy)}
    (key : Int32) (value : Atom Γ .i32) (row : Row Γ (.i32 :: types) joins) :
    Option (Row Γ types joins) :=
  match row with
  | @Row.mk _ _ _ index _ _ (.cons (.i32 candidate) rest) target arguments =>
      if key == candidate then some ⟨index, rest, target, arguments⟩ else none
  | row => defaultRow value row

private def heads {Γ : List ObjTy} {a : ObjTy} {types : List ObjTy} {joins : List (List ObjTy)}
    (rows : List (Row Γ (a :: types) joins)) :
    List ((fields : List ObjTy) × Constructor a fields) :=
  (rows.filterMap headConstructor?).foldl (init := []) fun found constructor =>
    if found.any (fun candidate => candidate.2.name == constructor.2.name) then found
    else found ++ [constructor]

private def complete (objects : ObjectCatalog) (a : ObjTy) (names : List Lean.Name) : Bool :=
  match a with
  | .option _ => names.contains ``Option.none && names.contains ``Option.some
  | .data id =>
      match objects.schema? id with
      | some schema => schema.constructors.all (fun constructor => names.contains constructor.name)
      | none => false
  | .unit | .bool | .i32 | .ref _ | .nbt _ | .nbtRef _ => false

private abbrev Used := Std.HashSet Nat

/--
Maranget specialization/default compilation with a leftmost-column heuristic. An irrefutable
first row becomes a jump immediately. RHS joins and default successors provide DAG sharing.
Integer tests use the same specialization, with a residual matrix excluding the tested
constant on the unequal edge. The recursive measure counts refutable patterns, then columns.
-/
private partial def compile {Γ types : List ObjTy} {joins : List (List ObjTy)} {result : ObjTy}
    (objects : ObjectCatalog)
    (values : Args (Atom Γ) types) (rows : List (Row Γ types joins)) :
    Option (Comp Γ result joins × Used) := do
  let first :: _ := rows | none
  if let some bindings := allBindings? first.patterns values then
    return (.jump first.target (first.arguments (.id Unit Γ) bindings), {first.index})
  match values with
  | .nil => none
  | .cons (a := .i32) value rest =>
      match rows.findSome? headI32? with
      | none => compile objects rest (rows.filterMap (defaultRow value))
      | some key => do
          let ρ := (Scope.Renaming.id Unit Γ).weaken .bool
          let tail := rest.map (fun value => value.rename ρ)
          let (yes, yesUsed) ← compile objects tail
            ((rows.filterMap (specializeI32 key value)).map (·.rename ρ))
          let (no, noUsed) ← compile objects (.cons (value.rename ρ) tail)
            ((rows.filter (fun row => headI32? row != some key)).map (·.rename ρ))
          pure (.letOp (.binary .eq value (.i32 key))
            (.branch (.local Scope.Var.head) yes no), yesUsed ∪ noUsed)
  | .cons (a := a) value rest =>
      let constructors := heads rows
      if constructors.isEmpty then
        compile objects rest (rows.filterMap (defaultRow value))
      else do
        let (fallback, used) : Arms Γ a result joins × Used ←
          if complete objects a (constructors.map (·.2.name)) then
            pure (Arms.nil, ({} : Used))
          else do
            let (body, used) ← compile objects rest (rows.filterMap (defaultRow value))
            pure (Arms.default body, used)
        let (arms, used) ← constructors.foldrM (init := (fallback, used)) fun ⟨fields, ctor⟩ (arms, used) => do
          let ρ := Scope.Renaming.appendRight Unit fields Γ
          let fields := (Scope.Var.identity Unit fields).map fun x =>
            Atom.local (Scope.Renaming.appendLeft Unit fields Γ x)
          let values := fields.append (rest.map (fun value => value.rename ρ))
          let specialized := rows.filterMap (specialize ctor value)
          let (body, branchUsed) ← compile objects values specialized
          pure (Arms.cons ctor body arms, used ∪ branchUsed)
        pure (.switch value arms, used)

/-- Compile one source matrix and diagnose uncovered values or unreachable source rows. -/
public def lower {Γ types : List ObjTy} {joins : List (List ObjTy)} {result : ObjTy}
    (source : Lean.Name) (objects : ObjectCatalog)
    (values : Args (Atom Γ) types) (rows : List (Row Γ types joins)) :
    Except Diagnostic (Comp Γ result joins) := do
  let some (body, used) := compile objects values rows
    | throw (.nonExhaustiveMatch source)
  if let some unused := rows.find? (fun row => !used.contains row.index) then
    throw (.redundantPattern source unused.index)
  pure body

end Oria.Lower.Pattern
