module

public import Oria.IR.Catalog.Function
public import Oria.Compiler.Lower.Pattern
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax

namespace Oria.Lower.ANF

open Oria.IR

/-- Nominal source binders paired with their values in the current scoped target context. -/
private structure Env (source target : List ObjTy) where
  definition : Lean.Name
  names : Args Local source
  values : Args (IR.Cont.Atom target) source

namespace Env

private def rename {source context target : List ObjTy}
    (environment : Env source context)
    (rho : Scope.Renaming Unit Unit context target) :
    Env source target :=
  { environment with
    values := environment.values.map fun value => value.rename rho }

private def extend {source target : List ObjTy} {a : ObjTy}
    (environment : Env source target)
    (name : Local a)
    (value : IR.Cont.Atom target a) :
    Env (a :: source) target :=
  { environment with
    names := .cons name environment.names
    values := .cons value environment.values }

private def prepend {source target added : List ObjTy}
    (environment : Env source target)
    (names : Args Local added)
    (values : Args (IR.Cont.Atom target) added) :
    Env (added ++ source) target :=
  { environment with
    names := names.append environment.names
    values := values.append environment.values }

private inductive Resolution (target : List ObjTy) (a : ObjTy) where
  | missing
  | unique (value : IR.Cont.Atom target a)
  | multiple

private def resolveIn {a : ObjTy} {source target : List ObjTy}
    (needle : Local a) :
    (names : Args Local source) →
    Args (IR.Cont.Atom target) source →
    Resolution target a
  | .nil, .nil => .missing
  | @Args.cons _ _ b _ name names,
      @Args.cons _ _ _ _ value values =>
      let tail := resolveIn needle names values
      if typeMatches : b = a then
        if typeMatches ▸ name = needle then
          match tail with
          | .missing => .unique (typeMatches ▸ value)
          | .unique _ | .multiple => .multiple
        else
          tail
      else
        tail

private def resolve {source target : List ObjTy} {a : ObjTy}
    (environment : Env source target)
    (name : Local a) : Except Diagnostic (IR.Cont.Atom target a) :=
  match resolveIn name environment.names environment.values with
  | .missing =>
      .error (.invalidLocalScope environment.definition a .unbound)
  | .unique value => .ok value
  | .multiple =>
      .error (.invalidLocalScope environment.definition a .ambiguous)

end Env

private def captureArgs {source target : List ObjTy}
    (rho : Scope.Renaming Unit Unit source target) :
    Args (IR.Cont.Atom target) source :=
  (Scope.Var.identity Unit source).map fun v =>
    .local (rho v)

/--
Flatten an expression left-to-right. The continuation is Kripke-indexed because evaluating an
expression may extend the ANF context before producing its atom.
-/
private def lowerExprK
    {source context : List ObjTy} {a : ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (environment : Env source context)
    (expression : IR.Tree.Expr a)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      IR.Cont.Atom target a →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  match expression with
  | .local name => do
      let value ← environment.resolve name
      next (Scope.Renaming.id Unit context) value
  | .unit => next (Scope.Renaming.id Unit context) .unit
  | .bool value => next (Scope.Renaming.id Unit context) (.bool value)
  | .i32 value => next (Scope.Renaming.id Unit context) (.i32 value)
  | .project (fields := fields) constructor field value =>
      lowerExprK environment value fun {target} ρ value => do
        let σ := Scope.Renaming.appendRight Unit fields target
        let body ← next (σ.comp ρ)
          (.local (Scope.Renaming.appendLeft Unit fields target field))
        pure (.switch value (.cons (.data constructor) body .nil))
  | .unary (b := b) operator value =>
      lowerExprK environment value fun rho value => do
        let body ← next (rho.weaken b) (.local Scope.Var.head)
        pure <|
          IR.Cont.Comp.letOp (.unary operator value) body
  | .binary (c := c) operator left right =>
      lowerExprK environment left fun leftRenaming leftValue =>
        lowerExprK (environment.rename leftRenaming) right fun rightRenaming rightValue => do
          let total := rightRenaming.comp leftRenaming
          let body ← next (total.weaken c) (.local Scope.Var.head)
          pure <|
            IR.Cont.Comp.letOp
              (.binary operator (leftValue.rename rightRenaming) rightValue)
              body

  | .ite condition yes no =>
      lowerExprK environment condition fun ρ condition => do
        let after ← next (ρ.weaken a) (.local Scope.Var.head)
        let yes ← lowerExprK (environment.rename ρ) yes fun σ result =>
          pure (IR.Cont.Comp.jump Scope.Var.head (.cons result (captureArgs σ)))
        let no ← lowerExprK (environment.rename ρ) no fun σ result =>
          pure (IR.Cont.Comp.jump Scope.Var.head (.cons result (captureArgs σ)))
        pure (.letJoin after (.branch condition yes no))
  termination_by sizeOf expression
  decreasing_by all_goals simp_wf <;> omega

private def lowerArgsK
    {source context types : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (environment : Env source context)
    (arguments : Args IR.Tree.Expr types)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      Args (IR.Cont.Atom target) types →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  match arguments with
  | .nil => next (Scope.Renaming.id Unit context) .nil
  | .cons value rest =>
      lowerExprK environment value fun valueRenaming value =>
        lowerArgsK (environment.rename valueRenaming) rest fun restRenaming loweredRest =>
          next (restRenaming.comp valueRenaming)
            (.cons (value.rename restRenaming) loweredRest)

/--
`Call.traverseK` fixes one output family for the whole traversal, while ANF hole evaluation
changes that family's lexical-context index. These private helpers are the minimum indexed,
left-to-right traversal missing from the command container API.
-/
private def lowerSegmentsK
    {source context : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (environment : Env source context)
    (segments : List (Command.Segment IR.Tree.Expr))
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      List (Command.Segment (IR.Cont.Atom target)) →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  match segments with
  | [] => next (Scope.Renaming.id Unit context) []
  | .token token :: rest =>
      lowerSegmentsK environment rest fun rho lowered =>
        next rho (.token token :: lowered)
  | .space :: rest =>
      lowerSegmentsK environment rest fun rho lowered =>
        next rho (.space :: lowered)
  | .i32 value :: rest =>
      lowerSegmentsK environment rest fun rho lowered =>
        next rho (.i32 value :: lowered)
  | .literal value :: rest =>
      lowerSegmentsK environment rest fun rho lowered =>
        next rho (.literal value :: lowered)
  | .hole codec value :: rest =>
      lowerExprK environment value fun valueRenaming value =>
        lowerSegmentsK (environment.rename valueRenaming) rest
          fun restRenaming lowered =>
            next (restRenaming.comp valueRenaming)
              (.hole codec (value.rename restRenaming) :: lowered)

private def lowerFragmentK
    {source context : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (environment : Env source context)
    (fragment : Command.Fragment IR.Tree.Expr)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      (lowered : Command.Fragment (IR.Cont.Atom target)) →
      lowered.requirements = fragment.requirements →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  lowerSegmentsK environment fragment.segments fun rho segments =>
    next rho ⟨segments, fragment.requirements⟩ rfl

private def lowerEncodedArgK
    {source context : List ObjTy} {key : Command.SlotKey} {result : ObjTy}
    {joins : List (List ObjTy)}
    (environment : Env source context)
    (argument : Command.EncodedArg IR.Tree.Expr key)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      (lowered : Command.EncodedArg (IR.Cont.Atom target) key) →
      lowered.requirements = argument.requirements →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  lowerFragmentK environment argument.fragment fun rho fragment same =>
    next rho ⟨fragment⟩ same

private def lowerEncodedArgsK
    {source context : List ObjTy} {schema : List Command.SlotKey} {result : ObjTy}
    {joins : List (List ObjTy)}
    (environment : Env source context)
    (arguments : Command.EncodedArgs IR.Tree.Expr schema)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      (lowered : Command.EncodedArgs (IR.Cont.Atom target) schema) →
      lowered.requirements = arguments.requirements →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  match arguments with
  | .nil => next (Scope.Renaming.id Unit context) .nil rfl
  | .cons argument rest =>
      lowerEncodedArgK environment argument fun argumentRenaming loweredArgument sameArgument =>
        lowerEncodedArgsK (environment.rename argumentRenaming) rest
          fun restRenaming loweredRest sameRest =>
            next (restRenaming.comp argumentRenaming)
              (.cons
                (loweredArgument.map fun value => value.rename restRenaming)
                loweredRest) (by
                  simp only [Command.EncodedArgs.requirements_cons,
                    Command.EncodedArg.map_requirements, sameArgument, sameRest])

private def lowerRequestK
    {source context : List ObjTy} {route : Command.Signature} {result : ObjTy}
    {joins : List (List ObjTy)}
    (environment : Env source context)
    (request : Command.Call IR.Tree.Expr route)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      (lowered : Command.Call (IR.Cont.Atom target) route) →
      lowered.grade = request.grade →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  lowerEncodedArgsK environment request.args fun rho arguments same =>
    next rho { request with args := arguments } (by
      simp [Command.Call.grade, Command.Call.requirements, same])

private def lowerPrimK
    {source context : List ObjTy} {primitiveGrade : Grade} {a : ObjTy} {result : ObjTy}
    {joins : List (List ObjTy)}
    (environment : Env source context)
    (primitive : IR.Tree.Prim primitiveGrade a)
    (next : ∀ {target},
      Scope.Renaming Unit Unit context target →
      IR.Cont.Op target primitiveGrade a →
      Except Diagnostic (IR.Cont.Comp target result joins)) :
    Except Diagnostic (IR.Cont.Comp context result joins) :=
  match primitive with
  | .division left right =>
      lowerExprK environment left fun rho left =>
        lowerExprK (environment.rename rho) right fun sigma right =>
          next (sigma.comp rho) (.division (left.rename sigma) right)
  | .checkpoint forced => next (Scope.Renaming.id Unit context) (.checkpoint forced)
  | .construct constructor arguments =>
      lowerArgsK environment arguments fun rho arguments =>
        next rho (.construct constructor arguments)
  | .call reference arguments =>
      lowerArgsK environment arguments fun rho arguments =>
        next rho (.call reference arguments)
  | .recur _ _ => .error .unloweredRecursion
  | .execute scope reference arguments =>
      lowerFragmentK environment scope.fragment fun rho fragment _ =>
        lowerArgsK (environment.rename rho) arguments fun sigma arguments =>
          next (sigma.comp rho) (.execute
            { scope with fragment := fragment.map (fun value => value.rename sigma) }
            reference arguments)
  | .command request =>
      lowerRequestK environment request fun rho request same =>
        next rho (same ▸ .command request)
  | .memory operation arguments =>
      lowerArgsK environment arguments fun rho arguments =>
        next rho (.memory operation arguments)

/-- The destination of a computation: function return or a typed join transfer. -/
private inductive Dest (Γ : List ObjTy) (joins : List (List ObjTy)) : ObjTy → ObjTy → Type where
  | ret {a : ObjTy} : Dest Γ joins a a
  | jump {a : ObjTy} {params : List ObjTy} {result : ObjTy} :
      Scope.Var Unit joins (a :: params) → Args (IR.Cont.Atom Γ) params →
      Dest Γ joins a result

namespace Dest

private def rename {Γ : List ObjTy} {joins : List (List ObjTy)} {a result : ObjTy}
    {Δ : List ObjTy}
    (dest : Dest Γ joins a result)
    (ρ : Scope.Renaming Unit Unit Γ Δ) : Dest Δ joins a result :=
  match dest with
  | .ret => .ret
  | .jump target values => .jump target (values.map (fun value => value.rename ρ))

private def weakenJoin {Γ : List ObjTy} {joins : List (List ObjTy)} {a result : ObjTy}
    (dest : Dest Γ joins a result) (params : List ObjTy) :
    Dest Γ (params :: joins) a result :=
  match dest with
  | .ret => .ret
  | .jump target values => .jump (target.weaken params) values

private def apply {Γ : List ObjTy} {joins : List (List ObjTy)} {a result : ObjTy}
    (dest : Dest Γ joins a result) (value : IR.Cont.Atom Γ a) :
    IR.Cont.Comp Γ result joins :=
  match dest with
  | .ret => .ret value
  | .jump target values => .jump target (.cons value values)

end Dest

/-- Lexical return destinations carry their captured atoms and scoped join references. -/
private structure Exits (Γ : List ObjTy) (result : ObjTy) (joins : List (List ObjTy)) where
  lookup : ∀ {a}, Local a → Option (Dest Γ joins a result)
  failure : Option (Dest Γ joins .unit result) := none

namespace Exits

private def empty {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)} :
    Exits Γ result joins := ⟨fun _ => none, none⟩

private def rename {Γ Δ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (exits : Exits Γ result joins) (ρ : Scope.Renaming Unit Unit Γ Δ) : Exits Δ result joins :=
  ⟨fun name => (exits.lookup name).map (·.rename ρ), exits.failure.map (·.rename ρ)⟩

private def weakenJoin {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (exits : Exits Γ result joins) (params : List ObjTy) : Exits Γ result (params :: joins) :=
  ⟨fun name => (exits.lookup name).map (·.weakenJoin params), exits.failure.map (·.weakenJoin params)⟩

private def bind {Γ : List ObjTy} {result a : ObjTy} {joins : List (List ObjTy)}
    (exits : Exits Γ result joins) (name : Local a) (dest : Dest Γ joins a result) :
    Exits Γ result joins :=
  { exits with lookup := fun {b} key =>
      if h : b = a then
        if h ▸ key = name then some (h.symm ▸ dest) else exits.lookup key
      else exits.lookup key }

private def failed {Γ : List ObjTy} {result : ObjTy} {joins : List (List ObjTy)}
    (exits : Exits Γ result joins) : IR.Cont.Comp Γ result joins :=
  match exits.failure with
  | none => .fail
  | some dest => dest.apply .unit

end Exits

mutual
  private def lowerTree
      {source context : List ObjTy} {grade : Grade} {a : ObjTy} {joins : List (List ObjTy)}
      {result : ObjTy}
      (objects : ObjectCatalog) (environment : Env source context)
      (exits : Exits context result joins)
      (tree : IR.Tree.TreeRep grade a) (dest : Dest context joins a result) :
      Except Diagnostic (IR.Cont.Comp context result joins) :=
    match tree with
    | .fail => pure exits.failed
    | .catching value handler => do
        let ρ := (Scope.Renaming.id Unit context).weaken .unit
        let recover ← lowerTree objects (environment.rename ρ) (exits.rename ρ) handler (dest.rename ρ)
        let exits := exits.weakenJoin (.unit :: context)
        let captured := captureArgs (Scope.Renaming.id Unit context)
        let value ← lowerTree objects environment
          { exits with failure := some (.jump Scope.Var.head captured) }
          value (dest.weakenJoin (.unit :: context))
        pure (.letJoin recover value)
    | .ret value =>
        lowerExprK environment value fun ρ value => pure ((dest.rename ρ).apply value)
    | .perform primitive =>
        lowerPrimK environment primitive fun ρ operation =>
          let body := (dest.rename (ρ.weaken a)).apply (.local Scope.Var.head)
          pure (if grade.canFail then .invoke operation body (exits.rename ρ).failed else .letOp operation body)
    | .bind name value body =>
        lowerWith objects environment exits value fun ρ value =>
          lowerTree objects ((environment.rename ρ).extend name value) (exits.rename ρ) body (dest.rename ρ)
    | .branch condition yes no =>
        lowerExprK environment condition fun ρ condition => do
          let environment := environment.rename ρ
          let yes ← lowerTree objects environment (exits.rename ρ) yes (dest.rename ρ)
          let no ← lowerTree objects environment (exits.rename ρ) no (dest.rename ρ)
          pure (.branch condition yes no)
    | .matchMany values rows =>
        lowerArgsK environment values fun ρ values =>
          lowerRows objects (environment.rename ρ) (exits.rename ρ) rows (dest.rename ρ) 0 fun _ rows =>
            Pattern.lower environment.definition objects values rows
    | .scoped _ _ => .error (.unsupportedMachineLowering environment.definition)
    | .fix _ _ _ _ => .error .unloweredRecursion
    | .weaken _ body => lowerTree objects environment exits body dest
    | .block target body => lowerTree objects environment (exits.bind target dest) body dest
    | .leave (a := a) target value => do
        let some target := exits.lookup target
          | .error (.invalidLocalScope environment.definition a .unbound)
        lowerExprK environment value fun ρ value => pure ((target.rename ρ).apply value)
  termination_by (sizeOf tree, 0)
  decreasing_by all_goals simp_wf <;> omega

  private def lowerWith
      {source context : List ObjTy} {grade : Grade} {a : ObjTy} {result : ObjTy}
      {joins : List (List ObjTy)}
      (objects : ObjectCatalog) (environment : Env source context)
      (exits : Exits context result joins)
      (tree : IR.Tree.TreeRep grade a)
      (next : ∀ {target}, Scope.Renaming Unit Unit context target →
        IR.Cont.Atom target a → Except Diagnostic (IR.Cont.Comp target result joins)) :
      Except Diagnostic (IR.Cont.Comp context result joins) :=
    match tree with
    | .fail => pure exits.failed
    | .catching value handler => lowerJoin objects environment exits (.catching value handler) next
    | .ret value => lowerExprK environment value next
    | .perform primitive =>
        lowerPrimK environment primitive fun ρ operation => do
          let body ← next (ρ.weaken a) (.local Scope.Var.head)
          pure (if grade.canFail then .invoke operation body (exits.rename ρ).failed else .letOp operation body)
    | .bind name value body =>
        lowerWith objects environment exits value fun ρ value =>
          lowerWith objects ((environment.rename ρ).extend name value) (exits.rename ρ) body fun σ value =>
            next (σ.comp ρ) value
    | .branch condition yes no => lowerJoin objects environment exits (.branch condition yes no) next
    | .matchMany values rows => lowerJoin objects environment exits (.matchMany values rows) next
    | .scoped _ _ => .error (.unsupportedMachineLowering environment.definition)
    | .fix _ _ _ _ => .error .unloweredRecursion
    | .weaken _ body => lowerWith objects environment exits body next
    | .block target body => lowerJoin objects environment exits (.block target body) next
    | .leave (a := a) target value => do
        let some target := exits.lookup target
          | .error (.invalidLocalScope environment.definition a .unbound)
        lowerExprK environment value fun ρ value => pure ((target.rename ρ).apply value)
  termination_by (sizeOf tree, 2)
  decreasing_by all_goals simp_wf <;> omega

  private def lowerJoin
      {source context : List ObjTy} {grade : Grade} {a : ObjTy} {result : ObjTy}
      {joins : List (List ObjTy)}
      (objects : ObjectCatalog) (environment : Env source context)
      (exits : Exits context result joins)
      (tree : IR.Tree.TreeRep grade a)
      (next : ∀ {target}, Scope.Renaming Unit Unit context target →
        IR.Cont.Atom target a → Except Diagnostic (IR.Cont.Comp target result joins)) :
      Except Diagnostic (IR.Cont.Comp context result joins) := do
    let body ← next ((Scope.Renaming.id Unit context).weaken a) (.local Scope.Var.head)
    let dest := Dest.jump (Scope.Var.head (Γ := joins))
      (captureArgs (Scope.Renaming.id Unit context))
    let paths ← lowerTree objects environment (exits.weakenJoin (a :: context)) tree dest
    pure (.letJoin body paths)
  termination_by (sizeOf tree, 1)
  decreasing_by all_goals simp_wf <;> omega

  /-- Each source RHS becomes one join whose parameters are its binders and lexical context. -/
  private def lowerRows
      {source context types : List ObjTy} {a : ObjTy} {grades : List Grade}
      {joins : List (List ObjTy)} {result : ObjTy}
      (objects : ObjectCatalog) (environment : Env source context)
      (exits : Exits context result joins)
      (rows : IR.Tree.RowsRep types a grades) (dest : Dest context joins a result)
      (index : Nat)
      (finish : ∀ {targets}, Scope.Renaming Unit Unit joins targets →
        List (Pattern.Row context types targets) →
        Except Diagnostic (IR.Cont.Comp context result targets)) :
      Except Diagnostic (IR.Cont.Comp context result joins) :=
    match rows with
    | .nil => finish (.id Unit joins) []
    | .cons (.mk (bindings := bindings) patterns names tree) rest => do
        let ρ := Scope.Renaming.appendRight Unit bindings context
        let parameters := (Scope.Var.identity Unit bindings).map fun x =>
          IR.Cont.Atom.local (Scope.Renaming.appendLeft Unit bindings context x)
        let env := (environment.rename ρ).prepend names parameters
        let body ← lowerTree objects env (exits.rename ρ) tree (dest.rename ρ)
        let params := bindings ++ context
        let next ← lowerRows objects environment (exits.weakenJoin params) rest (dest.weakenJoin params) (index + 1)
          fun σ rows =>
            let row : Pattern.Row context types _ := {
              index
              patterns
              target := σ Scope.Var.head
              arguments := fun ρ values => values.append (captureArgs ρ)
            }
            finish (σ.comp ((Scope.Renaming.id Unit joins).weaken params)) (row :: rows)
        pure (.letJoin body next)
  termination_by (sizeOf rows, 0)
  decreasing_by all_goals simp_wf <;> omega
end

/-- Resolve nominal locals, introduce ANF bindings, and compile source pattern matrices. -/
public def lower {functions : Function.Catalog} {commands : Command.Catalog}
    {objects : ObjectCatalog} {sig : Signature}
    (source : Lean.Name)
    (definition : Function.Catalog.LinkedDef functions commands objects sig) :
    Except Diagnostic (IR.Cont.Def sig) := do
  let tree := definition.commandLinked.objectLinked.treeDef
  let parameters := (Scope.Var.identity Unit sig.args).map IR.Cont.Atom.local
  let environment : Env sig.args sig.args :=
    { definition := source, names := tree.params, values := parameters }
  let computation ← lowerTree objects environment Exits.empty tree.body.rep .ret
  pure (IR.Cont.Def.build fun _ => computation)

end Oria.Lower.ANF
