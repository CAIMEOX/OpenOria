module

public import Oria.IR.Cont.Definition
import Oria.IR.Cont.Substitution

namespace Oria.Optimize.Cont

open Oria.IR Oria.IR.Cont Oria.IR.Cont.Subst

/-- A known constructor records its original payload atoms, retaining sharing. -/
private inductive Fact (Γ : List ObjTy) : ObjTy → Type where
  | unknown {a : ObjTy} : Fact Γ a
  | ctor {a : ObjTy} {fields : List ObjTy} :
      Constructor a fields → Args (Atom Γ) fields → Fact Γ a

private def Fact.rename {Γ : List ObjTy} {a : ObjTy} {Δ : List ObjTy}
    (fact : Fact Γ a) (ρ : Scope.Renaming Unit Unit Γ Δ) : Fact Δ a :=
  match fact with
  | .unknown => .unknown
  | .ctor ref args => .ctor ref (args.map (fun x => x.rename ρ))

private abbrev Facts (Γ : List ObjTy) := Args (Fact Γ) Γ

private def unknown (Γ : List ObjTy) : Facts Γ :=
  Args.tabulate Γ fun _ => .unknown

private def enter {Γ : List ObjTy} (facts : Facts Γ) (as : List ObjTy) : Facts (as ++ Γ) :=
  (Args.tabulate as fun _ => Fact.unknown (Γ := as ++ Γ)).append
    (facts.map fun f => f.rename (Scope.Renaming.appendRight Unit as Γ))

private def known {Γ : List ObjTy} {a : ObjTy} (facts : Facts Γ) : Atom Γ a → Fact Γ a
  | .local x => x.lookup facts
  | .unit | .bool _ | .i32 _ => .unknown

private def assume {Γ : List ObjTy} {a : ObjTy}
    (facts : Facts Γ) (value : Atom Γ a) (fact : Fact Γ a) : Facts Γ :=
  match value with
  | .local x => Args.tabulate Γ fun i =>
      if same : i = x.index then
        ((congrArg (fun j => Γ.get j) same).trans x.typeCorrect).symm ▸ fact
      else facts.get i
  | _ => facts

private def resultFact {Γ : List ObjTy} {g : Grade} {a : ObjTy} : Op Γ g a → Fact Γ a
  | .construct ref args => .ctor ref args
  | _ => .unknown

/-- Evaluate only total scalar operations, using the language's Int32 semantics. -/
private def constant {Γ : List ObjTy} {g : Grade} {a : ObjTy} : Op Γ g a → Option (Atom Γ a)
  | .copy value => some value
  | .unary .neg (.i32 x) => some (.i32 (-x))
  | .unary .not (.bool x) => some (.bool (!x))
  | .binary .add (.i32 x) (.i32 y) => some (.i32 (x + y))
  | .binary .sub (.i32 x) (.i32 y) => some (.i32 (x - y))
  | .binary .mul (.i32 x) (.i32 y) => some (.i32 (x * y))
  | .binary .le (.i32 x) (.i32 y) => some (.bool (decide (x ≤ y)))
  | .binary .lt (.i32 x) (.i32 y) => some (.bool (decide (x < y)))
  | .binary .eq (.i32 x) (.i32 y) => some (.bool (x == y))
  | .binary .beq (.bool x) (.bool y) => some (.bool (x == y))
  | .binary .add x (.i32 0) | .binary .add (.i32 0) x
  | .binary .sub x (.i32 0)
  | .binary .mul x (.i32 1) | .binary .mul (.i32 1) x => some x
  | .binary .mul _ (.i32 0) | .binary .mul (.i32 0) _ => some (.i32 0)
  | .binary .beq x (.bool true) | .binary .beq (.bool true) x => some x
  | _ => none

mutual
  private def simplify {Γ Δ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
      (σ : Subst Γ Δ) (facts : Facts Δ) :
      Comp Γ result joins → Comp Δ result joins
    | .fail => .fail
    | .invoke (a := a) op next failed =>
        match op.map (atom σ) with
        | .division (.i32 x) (.i32 y) =>
            match I32.divide x y with
            | some value => simplify (.cons (.i32 value) σ) facts next
            | none => simplify σ facts failed
        | op => .invoke op
            (simplify (lift σ [a]) (enter facts [a]) next) (simplify σ facts failed)
    | .ret value => .ret (atom σ value)
    | .jump target args => .jump target (args.map (atom σ))
    | .letOp (a := a) op next =>
        let op := op.map (atom σ)
        match constant op with
        | some value => simplify (.cons value σ) facts next
        | none =>
            let ρ := (Scope.Renaming.id Unit Δ).weaken a
            .letOp op (simplify (lift σ [a])
              (.cons ((resultFact op).rename ρ) (facts.map (fun f => f.rename ρ))) next)
    | .branch value yes no =>
        match atom σ value with
        | .bool true => simplify σ facts yes
        | .bool false => simplify σ facts no
        | value => .branch value (simplify σ facts yes) (simplify σ facts no)
    | .switch value arms =>
        let value := atom σ value
        match known facts value with
        | .unknown => .switch value (simplifyArms σ facts value arms)
        | .ctor ref args => select σ facts value ref args arms
    | .letJoin (params := params) body next =>
        .letJoin (simplify (identity params) (unknown params) body) (simplify σ facts next)

  private def simplifyArms {Γ Δ : List ObjTy} {a : ObjTy} {result : ObjTy}
      {joins : List (List ObjTy)}
      (σ : Subst Γ Δ) (facts : Facts Δ) (value : Atom Δ a) :
      Arms Γ a result joins → Arms Δ a result joins
    | .nil => .nil
    | .default body => .default (simplify σ facts body)
    | .cons (fields := fields) ref body rest =>
        let args := (Scope.Var.identity Unit fields).map fun x =>
          Atom.local (Scope.Renaming.appendLeft Unit fields Δ x)
        let facts' := assume (enter facts fields) (value.weakenMany fields) (.ctor ref args)
        .cons ref (simplify (lift σ fields) facts' body)
          (simplifyArms σ facts value rest)

  private def select {Γ Δ : List ObjTy} {a : ObjTy} {fields : List ObjTy}
      {result : ObjTy} {joins : List (List ObjTy)}
      (σ : Subst Γ Δ) (facts : Facts Δ) (value : Atom Δ a)
      (ref : Constructor a fields) (args : Args (Atom Δ) fields) :
      Arms Γ a result joins → Comp Δ result joins
    | .nil => .switch value .nil
    | .default body => simplify σ facts body
    | .cons (fields := other) candidate body rest =>
        if same : fields = other then
          if ref.name == candidate.name then
            simplify ((same ▸ args).append σ) facts body
          else select σ facts value ref args rest
        else select σ facts value ref args rest
end

/-- Substitute copies and scalar constants, then reduce known Boolean and constructor branches. -/
public def run {sig : Signature} (definition : Def sig) : Def sig :=
  Def.build fun _ => simplify (identity sig.args) (unknown sig.args) definition.computation

end Oria.Optimize.Cont
