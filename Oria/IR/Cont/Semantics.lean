module

public import Oria.IR.Cont.Support

namespace Oria.Semantics.Cont

open Oria Oria.IR Oria.IR.Cont

public structure DataValue (_id : TypeId) where
  token : Nat

public inductive Value : ObjTy → Type where
  | unit : Value .unit
  | bool : Bool → Value .bool
  | i32 : Int32 → Value .i32
  | nbt {t : Option Nbt.Tag} : Nbt.ValueAt t → Value (.nbt t)
  | nbtRef {s : Nbt.Schema} : Nat → Value (.nbtRef s)
  | ref {a : ObjTy} : Nat → Value (.ref a)
  | none {a : ObjTy} : Value (.option a)
  | some {a : ObjTy} : Value a → Value (.option a)
  | data {owner : TypeId} : DataValue owner → Value (.data owner)

public inductive Result (a : ObjTy) where
  | returned : Value a → Result a
  | failed : Result a

/-- Runtime values aligned definitionally with a lexical object-type context. -/
public abbrev Env (Γ : List ObjTy) := Args Value Γ

namespace Env

@[expose] public def lookup {Γ : List ObjTy} {a : ObjTy}
    (env : Env Γ) (x : Scope.Var Unit Γ a) : Value a :=
  x.lookup env

@[expose] public def extend {Γ : List ObjTy} {a : ObjTy} (env : Env Γ) (value : Value a) : Env (a :: Γ) :=
  .cons value env

end Env

public abbrev JoinEnv (result : ObjTy) (joins : List (List ObjTy)) (s : Type := Unit) :=
  Args (fun params => Args Value params → Nat → StateM s (Option (Result result))) joins

@[expose] public def atom {Γ : List ObjTy} {a : ObjTy} (env : Env Γ) : Atom Γ a → Value a
  | .local x => env.lookup x
  | .unit => .unit
  | .bool value => .bool value
  | .i32 value => .i32 value

@[simp] public theorem atom_local {Γ : List ObjTy} {a : ObjTy} (env : Env Γ) (x : Scope.Var Unit Γ a) :
    atom env (.local x) = env.lookup x := rfl

public structure Model (s : Type := Unit) where
  checkpoint : Bool → StateM s (Result .unit) := fun _ => pure (.returned .unit)
  unary : ∀ {a b}, UnaryOp a b → Value a → StateM s (Result b)
  binary : ∀ {a b c}, BinaryOp a b c → Value a → Value b → StateM s (Result c)
  construct : ∀ {owner fields},
    CtorRef owner fields → Args Value fields → StateM s (Result (.data owner))
  call : ∀ {sig}, DeclRef sig → Args Value sig.args → StateM s (Result sig.result)
  command : ∀ {route}, Command.Call Value route → StateM s (Result .i32)
  execute : ∀ {params g}, Execute.Scope Value → DeclRef ⟨params, .i32, g⟩ →
    Args Value params → StateM s (Result .unit)
  memory : ∀ {g fields a},
    MemoryOp g fields a → Args Value fields → StateM s (Result a)
  project : ∀ {owner fields},
    CtorRef owner fields → DataValue owner → StateM s (Option (Args Value fields))

@[expose] public def evalArgs {Γ : List ObjTy} {types : List ObjTy}
    (env : Env Γ) (values : Args (Atom Γ) types) : Args Value types :=
  values.map (atom env)

@[expose] public def evalOp {s : Type} {Γ : List ObjTy} {g : Grade} {a : ObjTy}
    (model : Model s) (env : Env Γ) : Op Γ g a → StateM s (Result a)
  | .division left right =>
      let .i32 left := atom env left
      let .i32 right := atom env right
      pure <| match I32.divide left right with
        | some value => .returned (.i32 value)
        | none => .failed
  | .checkpoint forced => model.checkpoint forced
  | .copy value => pure (.returned (atom env value))
  | .unary op value => model.unary op (atom env value)
  | .binary op left right => model.binary op (atom env left) (atom env right)
  | .construct (.data constructor) args => model.construct constructor (evalArgs env args)
  | .construct .none .nil => pure (.returned .none)
  | .construct .some (.cons value .nil) => pure (.returned (.some (atom env value)))
  | .call ref args => model.call ref (evalArgs env args)
  | .memory operation args => model.memory operation (evalArgs env args)
  | .command request => model.command (request.map (atom env))
  | .execute scope ref args => model.execute (scope.map (atom env)) ref (evalArgs env args)

/-- Constructor testing exposes exactly the payload telescope of the successful arm. -/
@[expose] public def project {s : Type} {a : ObjTy} {fields : List ObjTy}
    (model : Model s) (constructor : Constructor a fields)
    (value : Value a) : StateM s (Option (Args Value fields)) :=
  match constructor, value with
  | .data ref, .data value => model.project ref value
  | .none, .none => pure (some .nil)
  | .some, .some value => pure (some (.cons value .nil))
  | .none, .some _ | .some, .none => pure none

mutual
  @[expose] public def eval {s : Type} {Γ : List ObjTy} {result : ObjTy} {scope : List (List ObjTy)}
      (model : Model s) (fuel : Nat) (env : Env Γ)
      (joins : JoinEnv result scope s) (computation : Comp Γ result scope) :
      StateM s (Option (Result result)) :=
    match fuel with
    | 0 => pure none
    | fuel + 1 =>
        match computation with
        | .fail => pure (some .failed)
        | .invoke operation next failed => do
            match ← evalOp model env operation with
            | .returned value => eval model fuel (env.extend value) joins next
            | .failed => eval model fuel env joins failed
        | .ret value => pure (some (.returned (atom env value)))
        | .letOp operation next =>
            do
              match ← evalOp model env operation with
              | .failed => pure (some .failed)
              | .returned value => eval model fuel (env.extend value) joins next
        | .branch condition yes no =>
            match atom env condition with
            | .bool true => eval model fuel env joins yes
            | .bool false => eval model fuel env joins no
        | .switch value arms => evalArms model fuel env joins (atom env value) arms
        | .letJoin body next =>
            eval model fuel env
              (.cons (fun arguments remaining => eval model remaining arguments joins body) joins) next
        | .jump target values => target.lookup joins (evalArgs env values) fuel
  termination_by structural computation

  @[expose] public def evalArms {s : Type} {Γ : List ObjTy} {result : ObjTy} {scope : List (List ObjTy)}
      {a : ObjTy}
      (model : Model s) (fuel : Nat) (env : Env Γ)
      (joins : JoinEnv result scope s) (value : Value a) (arms : Arms Γ a result scope) :
      StateM s (Option (Result result)) :=
    match fuel with
    | 0 => pure none
    | fuel + 1 =>
        match arms with
        | .nil => pure (some .failed)
        | .default body => eval model fuel env joins body
        | .cons constructor body rest =>
            do
              match ← project model constructor value with
              | none => evalArms model fuel env joins value rest
              | some fields => eval model fuel (fields.append env) joins body
  termination_by structural arms
end

@[simp] public theorem eval_ret {Γ : List ObjTy} {result : ObjTy} {s : Type}
    {model : Model s} {fuel : Nat} {env : Env Γ} {scope : List (List ObjTy)}
    {joins : JoinEnv result scope s} (value : Atom Γ result) :
    eval model (fuel + 1) env joins (Comp.ret value) =
      pure (some (.returned (atom env value))) := rfl

@[simp] public theorem eval_letOp {Γ : List ObjTy} {g : Grade} {a result : ObjTy}
    {scope : List (List ObjTy)} {s : Type} {model : Model s} {fuel : Nat} {env : Env Γ}
    {joins : JoinEnv result scope s}
    (operation : Op Γ g a)
    (next : Comp (a :: Γ) result scope) :
    eval model (fuel + 1) env joins (Comp.letOp operation next) =
      (do
        match ← evalOp model env operation with
        | .failed => pure (some .failed)
        | .returned value => eval model fuel (env.extend value) joins next) := by
      rfl

@[simp] public theorem eval_branch {Γ : List ObjTy} {result : ObjTy} {scope : List (List ObjTy)}
    {s : Type} {model : Model s} {fuel : Nat} {env : Env Γ} {joins : JoinEnv result scope s}
    (condition : Atom Γ .bool)
    (yes no : Comp Γ result scope) :
    eval model (fuel + 1) env joins (Comp.branch condition yes no) =
      match atom env condition with
      | .bool true => eval model fuel env joins yes
      | .bool false => eval model fuel env joins no := rfl

@[simp] public theorem eval_letJoin {params : List ObjTy} {result : ObjTy} {scope : List (List ObjTy)}
    {Γ : List ObjTy} {s : Type} {model : Model s} {fuel : Nat} {env : Env Γ}
    {joins : JoinEnv result scope s}
    (body : Comp params result scope)
    (next : Comp Γ result (params :: scope)) :
    eval model (fuel + 1) env joins (Comp.letJoin body next) =
      eval model fuel env
        (.cons (fun arguments remaining => eval model remaining arguments joins body) joins) next := rfl

@[simp] public theorem eval_jump {scope : List (List ObjTy)} {params Γ : List ObjTy} {s : Type}
    {model : Model s} {fuel : Nat} {env : Env Γ} {result : ObjTy}
    {joins : JoinEnv result scope s}
    (target : Scope.Var Unit scope params)
    (arguments : Args (Atom Γ) params) :
    eval model (fuel + 1) env joins (Comp.jump target arguments) =
      target.lookup joins (evalArgs env arguments) fuel := rfl

end Oria.Semantics.Cont
