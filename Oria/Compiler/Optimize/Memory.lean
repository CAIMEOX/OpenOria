module

public import Oria.IR.Cont.Definition
import Oria.IR.Cont.Substitution
import Oria.Compiler.Analysis.Memory

namespace Oria.Optimize.Memory

open Oria.IR Oria.IR.Cont Oria.IR.Cont.Subst Oria.Analysis.Memory

/-- Successful selections establish presence, optionally with an observed scalar.
The Boolean distinguishes I32 reads from native size measurements. -/
private structure Fact (Γ : List ObjTy) where
  location : Location Γ
  value : Option (Bool × Atom Γ .i32) := none

private abbrev Facts (Γ : List ObjTy) := List (Fact Γ)

private def enter {Γ : List ObjTy} (facts : Facts Γ) (as : List ObjTy) : Facts (as ++ Γ) :=
  let ρ := Scope.Renaming.appendRight Unit as Γ
  facts.map fun f => ⟨f.location.rename ρ, f.value.map fun (mode, value) => (mode, value.rename ρ)⟩

private def establish {Γ : List ObjTy} (facts : Facts Γ) (loc : Location Γ)
    (value : Option (Bool × Atom Γ .i32) := none) : Facts Γ :=
  ⟨loc, value⟩ :: facts

private def known {Γ : List ObjTy} (facts : Facts Γ) (loc : Location Γ)
    (numeric : Bool) : Option (Atom Γ .i32) :=
  facts.findSome? fun f =>
    if f.location.same loc then f.value.bind fun (mode, value) =>
      if mode == numeric then some value else none
    else none

private def checkedPath {Γ as : List ObjTy} (facts : Facts Γ) (loc : Location Γ)
    (path : IR.Nbt.Path (Scope.Var Unit as .i32)) : IR.Nbt.Path (Scope.Var Unit as .i32) :=
  if facts.any (fun f => f.location.same loc) then { path with check := .available } else path

/-- Retain facts only for separated address spaces or path footprints. -/
private def invalidate {Γ : List ObjTy} (facts : Facts Γ) (loc : Location Γ) : Facts Γ :=
  facts.filter fun f => f.location.separate loc

private def writeValue {Γ as : List ObjTy} (args : Args (Atom Γ) as) :
    IR.Nbt.Write (Scope.Var Unit as .i32) → Option (Bool × Atom Γ .i32)
  | .i32 value => some (true, value.lookup args)
  | .literal ⟨.int, .int value⟩ => some (true, .i32 value)
  | _ => none

private structure Step (Γ : List ObjTy) (g : Grade) (a : ObjTy) where
  op : Op Γ g a
  failed : Facts Γ
  normal : Facts (a :: Γ)
  value : Option (Atom Γ a) := none

private def preserve {Γ : List ObjTy} {g : Grade} {a : ObjTy}
    (facts : Facts Γ) (op : Op Γ g a) : Step Γ g a :=
  ⟨op, facts, enter facts [a], none⟩

private def step {Γ : List ObjTy} {g : Grade} {a : ObjTy}
    (facts : Facts Γ) (op : Op Γ g a) : Step Γ g a :=
  match op with
  | op@(.copy value) => { preserve facts op with value := some value }
  | op@(.unary ..) | op@(.binary ..) | op@(.division ..) | op@(.construct ..) => preserve facts op
  | .memory (.nbt (.inspectRef root path numeric)) args =>
      let loc := Location.ofPath args root path
      let path := checkedPath facts loc path
      let next := establish (enter facts [.i32])
        (loc.rename ((Scope.Renaming.id Unit Γ).weaken .i32)) (some (numeric, .local .head))
      ⟨.memory (.nbt (.inspectRef root path numeric)) args, facts, next, known facts loc numeric⟩
  | .memory (.nbt (.putRef root path value append)) args =>
      let loc := Location.ofPath args root path
      let failed := invalidate facts loc
      let next := establish failed loc (if append then none else writeValue args value)
      ⟨.memory (.nbt (.putRef root path value append)) args, failed, enter next [.unit], none⟩
  | .memory (.nbt (.clearRef root path)) args =>
      let loc := Location.ofPath args root path
      let failed := invalidate facts loc
      let next := establish failed loc (some (false, .i32 0))
      ⟨.memory (.nbt (.clearRef root path)) args, failed, enter next [.unit], none⟩
  | .memory (.nbt (.copyRef dst path src selected append)) args =>
      let loc := Location.ofPath args dst path
      let source := Location.ofPath args src selected
      let failed := invalidate facts loc
      let value := if append then none else (known facts source true).map (true, ·)
      let next := establish failed loc value
      ⟨.memory (.nbt (.copyRef dst path src selected append)) args, failed, enter next [.unit], none⟩
  | .memory (.nbt (.read mode (.reference root path))) args =>
      let loc := Location.ofPath args root path
      let path := checkedPath facts loc path
      let next := if mode == .one then establish facts loc else facts
      ⟨.memory (.nbt (.read mode (.reference root path))) args, facts, enter next [.nbt mode.tag], none⟩
  | op@(.memory (.nbt (.newRef ..)) _)
  | op@(.memory (.nbt (.inspectValue ..)) _)
  | op@(.memory (.nbt (.literal ..)) _)
  | op@(.memory (.nbt .integer) _)
  | op@(.memory (.nbt .forget) _)
  | op@(.memory (.nbt .number) _) => preserve facts op
  | op => preserve [] op

mutual
  private def simplify {Γ Δ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
      (σ : Subst Γ Δ) (facts : Facts Δ) : Comp Γ result joins → Comp Δ result joins
    | .fail => .fail
    | .ret value => .ret (atom σ value)
    | .jump target args => .jump target (args.map (atom σ))
    | .invoke (a := a) op next failed =>
        let info := step facts (op.map (atom σ))
        match info.value with
        | some value => simplify (.cons value σ) facts next
        | none => .invoke info.op (simplify (lift σ [a]) info.normal next)
            (simplify σ info.failed failed)
    | .letOp (a := a) op next =>
        let info := step facts (op.map (atom σ))
        match info.value with
        | some value => simplify (.cons value σ) facts next
        | none => .letOp info.op (simplify (lift σ [a]) info.normal next)
    | .branch value yes no => .branch (atom σ value) (simplify σ facts yes) (simplify σ facts no)
    | .switch value arms => .switch (atom σ value) (simplifyArms σ facts arms)
    | .letJoin (params := params) body next =>
        .letJoin (simplify (identity params) [] body) (simplify σ facts next)

  private def simplifyArms {Γ Δ : List ObjTy} {a result : ObjTy} {joins : List (List ObjTy)}
      (σ : Subst Γ Δ) (facts : Facts Δ) : Arms Γ a result joins → Arms Δ a result joins
    | .nil => .nil
    | .default body => .default (simplify σ facts body)
    | .cons (fields := fields) ref body rest =>
        .cons ref (simplify (lift σ fields) (enter facts fields) body) (simplifyArms σ facts rest)
end

/-- Forward owned-document scalar reads and carry established selection checks into Machine.
Calls, external commands, suspension, and join bodies start a fresh memory-fact scope. -/
public def run {sig : Signature} (definition : Def sig) : Def sig :=
  if sig.grade.eff &&& (Eff.memoryRead ||| Eff.memoryWrite) == Eff.none then definition
  else Def.build fun _ => simplify (identity sig.args) [] definition.computation

end Oria.Optimize.Memory
