module

public import Oria.IR.Tree.Definition
import all Oria.IR.Tree.Definition
import all Oria.IR.Tree.Syntax
public import Std.Data.HashSet.Lemmas

namespace Oria.IR.Tree

/-- One typed runtime call edge retained exactly as it occurs in Tree. -/
public abbrev FunctionDependency := DeclRef.Some

/-- One typed command edge retained exactly as it occurs in Tree. -/
public structure CommandDependency where
  sig : Command.Signature
  ref : Command.Ref sig

/-- Direct typed dependencies observed in one Tree definition. -/
public structure Dependencies where
  functions : Array FunctionDependency
  objectTypes : Std.HashSet TypeId
  commands : Array CommandDependency
  roots : Array RootRef.Some := #[]
  globals : Array Nbt.GlobalRef := #[]
  persistentTypes : Std.HashSet ObjTy := {}

namespace Dependencies

@[expose] public def empty : Dependencies :=
  { functions := #[], objectTypes := {}, commands := #[] }

@[expose] public def combine (left right : Dependencies) : Dependencies :=
  { functions := left.functions ++ right.functions
    objectTypes := left.objectTypes ∪ right.objectTypes
    commands := left.commands ++ right.commands
    roots := left.roots ++ right.roots
    globals := left.globals ++ right.globals
    persistentTypes := left.persistentTypes ∪ right.persistentTypes }

public theorem function_not_mem_empty (dependency : FunctionDependency) :
    dependency ∉ empty.functions := by
  simp [empty]

public theorem command_not_mem_empty (dependency : CommandDependency) :
    dependency ∉ empty.commands := by
  simp [empty]

public theorem object_not_mem_empty (id : TypeId) :
    id ∉ empty.objectTypes := by
  simp [empty]

public theorem function_mem_combine {left right : Dependencies} (dependency : FunctionDependency) :
    dependency ∈ (combine left right).functions ↔
      dependency ∈ left.functions ∨ dependency ∈ right.functions := by
  simp [combine]

public theorem command_mem_combine {left right : Dependencies} (dependency : CommandDependency) :
    dependency ∈ (combine left right).commands ↔
      dependency ∈ left.commands ∨ dependency ∈ right.commands := by
  simp [combine]

public theorem object_mem_combine {left right : Dependencies} (id : TypeId) :
    (combine left right).objectTypes.contains id ↔
      left.objectTypes.contains id ∨ right.objectTypes.contains id := by
  simp [combine]

private def ofType : ObjTy → Dependencies
  | .unit | .bool | .i32 | .nbt _ | .nbtRef _ => empty
  | .option element | .ref element => ofType element
  | .data id => { empty with objectTypes := {id} }

private def ofTypes : List ObjTy → Dependencies
  | [] => empty
  | ty :: types => combine (ofType ty) (ofTypes types)

private def ofSignature (sig : Signature) : Dependencies :=
  combine (ofTypes sig.args) (ofType sig.result)

private def ofExpr {a : ObjTy} : Expr a → Dependencies
  | .local _ => ofType a
  | .unit | .bool _ | .i32 _ => empty
  | .unary _ value => ofExpr value
  | .binary _ left right => combine (ofExpr left) (ofExpr right)
  | .ite condition yes no => combine (ofExpr condition) (combine (ofExpr yes) (ofExpr no))
  | .project (owner := owner) (fields := fields) _ _ value =>
      combine (ofType (.data owner)) (combine (ofTypes fields) (ofExpr value))

private def ofArgs {types : List ObjTy} (arguments : Args Expr types) : Dependencies :=
  arguments.foldl (fun dependencies expression =>
    combine dependencies (ofExpr expression)) empty

private def ofRequest {sig : Command.Signature} (request : Command.Call Expr sig) : Dependencies :=
  let holes := request.traverseK
    (fun expression next => combine (ofExpr expression) (next expression))
    (fun _ => empty)
  combine
    { empty with
      commands := #[{ sig, ref := request.ref }] }
    holes

private def ofPrim {g : Grade} {a : ObjTy} : Prim g a → Dependencies
  | .division left right => combine (ofExpr left) (ofExpr right)
  | .checkpoint _ => empty
  | .construct (a := a) (fields := fields) _ arguments =>
      combine (ofType a) <|
        combine (ofTypes fields) (ofArgs arguments)
  | .call (sig := sig) ref arguments =>
      combine
        { (ofSignature sig) with functions := #[{ sig, ref }] }
        (ofArgs arguments)
  | .recur (sig := sig) _ arguments => combine (ofSignature sig) (ofArgs arguments)
  | .execute (params := params) (g := g) scope ref arguments =>
      let holes := scope.traverseK
        (fun expression next => combine (ofExpr expression) (next expression)) (fun _ => empty)
      combine { (ofSignature ⟨params, .i32, g⟩) with functions := #[⟨_, ref⟩] }
        (combine (ofArgs arguments) holes)
  | .command request => ofRequest request
  | .memory (fields := fields) (.nbt op) arguments =>
      { combine (ofType a) (combine (ofTypes fields) (ofArgs arguments)) with globals := op.globals }
  | .memory (fields := fields) operation arguments =>
      { combine (ofType a) (combine (ofTypes fields) (ofArgs arguments)) with
        roots := operation.root?.toArray
        persistentTypes := Std.HashSet.ofList (a :: fields) }

mutual
  private def ofPattern {a : ObjTy} {bindings : List ObjTy} : Pattern a bindings → Dependencies
    | .any | .bind | .i32 _ => ofType a
    | .ctor _ fields => combine (ofType a) (ofPatterns fields)

  private def ofPatterns {types : List ObjTy} {bindings : List ObjTy} :
      Patterns types bindings → Dependencies
    | .nil => empty
    | .cons head rest => combine (ofPattern head) (ofPatterns rest)
end

mutual
  private def ofTreeRep {g : Grade} {a : ObjTy} : TreeRep g a → Dependencies
    | .fail => ofType a
    | .catching body handler => combine (ofTreeRep body) (ofTreeRep handler)
    | .ret value => combine (ofType a) (ofExpr value)
    | .perform primitive => combine (ofType a) (ofPrim primitive)
    | .weaken _ body => ofTreeRep body
    | .block _ body => ofTreeRep body
    | .leave _ value => combine (ofType a) (ofExpr value)
    | .bind (a := a) _ value body =>
        combine (ofType a) <| combine (ofTreeRep value) (ofTreeRep body)
    | .branch condition yes no =>
        combine (ofExpr condition) <| combine (ofTreeRep yes) (ofTreeRep no)
    | .matchMany values rows => combine (ofArgs values) (ofRowsRep rows)
    | .scoped scope body =>
        scope.traverseK
          (fun expression next => combine (ofExpr expression) (next expression))
          (fun _ => ofTreeRep body)
    | .fix (sig := sig) _ _ body args =>
        combine (ofSignature sig) (combine (ofTreeRep body) (ofArgs args))

  private def ofRowRep {types : List ObjTy} {result : ObjTy} {g : Grade} :
      RowRep types result g → Dependencies
    | .mk patterns _ body => combine (ofPatterns patterns) (ofTreeRep body)

  private def ofRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade} :
      RowsRep types result grades → Dependencies
    | .nil => empty
    | .cons row rest => combine (ofRowRep row) (ofRowsRep rest)
end

/-- Observe a definition signature and body without expanding registries or schemas. -/
public def ofDefinition {sig : Signature} (definition : Def sig) : Dependencies :=
  combine (ofSignature sig) (ofTreeRep definition.body.rep)

end Dependencies

namespace Def

public def dependencies {sig : Signature} (definition : Def sig) : Dependencies :=
  Dependencies.ofDefinition definition

end Def

end Oria.IR.Tree
