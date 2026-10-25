module

public import Oria.Command.Syntax
public import Oria.Command.Execute
public import Oria.IR.Common.Local
public import Oria.IR.Common.Operator
public import Oria.IR.Common.Reference
public import Oria.IR.Common.Memory
public import Oria.IR.Common.Scope
public import Oria.IR.Tree.Pattern

namespace Oria.IR.Tree

/-- Source-shaped values. Pure expressions remain nested until ANF lowering. -/
public inductive Expr : ObjTy → Type where
  | local {a : ObjTy} : Local a → Expr a
  | unit : Expr .unit
  | bool : Bool → Expr .bool
  | i32 : Int32 → Expr .i32
  | unary {a b : ObjTy} : UnaryOp a b → Expr a → Expr b
  | binary {a b c : ObjTy} : BinaryOp a b c → Expr a → Expr b → Expr c
  | ite {a : ObjTy} : Expr .bool → Expr a → Expr a → Expr a
  | project {owner : TypeId} {fields : List ObjTy} {a : ObjTy} :
      CtorRef owner fields → Scope.Var Unit fields a → Expr (.data owner) → Expr a

/-- Typed primitive computations, indexed by their exact logical grade and result. -/
public inductive Prim : Grade → ObjTy → Type where
  | division : Expr .i32 → Expr .i32 → Prim .failure .i32
  | checkpoint : (forced : Bool) → Prim .suspension .unit
  | construct {a : ObjTy} {fields : List ObjTy} :
      Constructor a fields → Args Expr fields → Prim .pure a
  | call {sig : Signature} : DeclRef sig → Args Expr sig.args → Prim sig.grade sig.result
  | recur {sig : Signature} : Local sig → Args Expr sig.args → Prim sig.grade sig.result
  | execute {params : List ObjTy} {g : Grade} : (scope : Execute.Scope Expr) →
      DeclRef ⟨params, .i32, g⟩ → Args Expr params → Prim (scope.grade g) .unit
  | memory {g : Grade} {fields : List ObjTy} {a : ObjTy} :
      MemoryOp g fields a → Args Expr fields → Prim g a
  | command {route : Command.Signature} :
      (request : Command.Call Expr route) →
      Prim request.grade .i32

mutual
  private inductive TreeRep : Grade → ObjTy → Type where
    | fail {a : ObjTy} : TreeRep .failure a
    | catching {g h : Grade} {a : ObjTy} :
        TreeRep g a → TreeRep h a → TreeRep (g.handled.seq h) a
    | ret {a : ObjTy} : Expr a → TreeRep .pure a
    | perform {g : Grade} {a : ObjTy} : Prim g a → TreeRep g a
    | bind {a : ObjTy} {g₁ : Grade} {g₂ : Grade} {b : ObjTy} :
        Local a →
        TreeRep g₁ a →
        TreeRep g₂ b →
        TreeRep (g₁.seq g₂) b
    | branch {g₁ : Grade} {a : ObjTy} {g₂ : Grade} :
        Expr .bool →
        TreeRep g₁ a →
        TreeRep g₂ a →
        TreeRep (g₁.join g₂) a
    | matchMany {types : List ObjTy} {a : ObjTy} {grade : Grade} {grades : List Grade} :
        Args Expr types → RowsRep types a (grade :: grades) →
        TreeRep (Grade.joins (grade :: grades)) a
    | scoped {g : Grade} : (scope : Execute.Scope Expr) → TreeRep g .i32 →
        TreeRep (scope.grade g) .unit
    | fix {sig : Signature} : Local sig → Args Local sig.args →
        TreeRep sig.grade sig.result → Args Expr sig.args → TreeRep sig.grade sig.result
    | weaken {g h : Grade} {a : ObjTy} : g.Below h → TreeRep g a → TreeRep h a
    | block {g : Grade} {a : ObjTy} : Local a → TreeRep g a → TreeRep g a
    | leave {a b : ObjTy} : Local a → Expr a → TreeRep .pure b

  private inductive RowRep : List ObjTy → ObjTy → Grade → Type where
    | mk {types : List ObjTy} {bindings : List ObjTy} {g : Grade} {result : ObjTy} :
        Patterns types bindings → Args Local bindings →
        TreeRep g result → RowRep types result g

  private inductive RowsRep : List ObjTy → ObjTy → List Grade → Type where
    | nil {types : List ObjTy} {result : ObjTy} : RowsRep types result []
    | cons {types : List ObjTy} {result : ObjTy} {g : Grade} {gs : List Grade} :
        RowRep types result g → RowsRep types result gs →
        RowsRep types result (g :: gs)
end

/-- Structured source computation. Its representation contains no ANF joins or jumps. -/
public structure Tree (g : Grade) (a : ObjTy) where
  private mk ::
  private rep : TreeRep g a

public structure Row (types : List ObjTy) (result : ObjTy) (g : Grade) where
  private mk ::
  private rep : RowRep types result g

public structure Rows (types : List ObjTy) (result : ObjTy) (grades : List Grade) where
  private mk ::
  private rep : RowsRep types result grades

namespace Tree

public def fail {a : ObjTy} : Tree .failure a := private_decl% ⟨.fail⟩

public def catching {g h : Grade} {a : ObjTy} (body : Tree g a) (handler : Tree h a) :
    Tree (g.handled.seq h) a := private_decl% ⟨.catching body.rep handler.rep⟩

/-- A lexical exit returns its payload to the named block, independently of the local result. -/
public def leave {a b : ObjTy} (target : Local a) (value : Expr a) : Tree .pure b :=
  private_decl% ⟨.leave target value⟩

public def ret {a : ObjTy} (value : Expr a) : Tree .pure a :=
  private_decl% ⟨.ret value⟩

public def perform {g : Grade} {a : ObjTy} (primitive : Prim g a) : Tree g a :=
  private_decl% ⟨.perform primitive⟩

public def branch
    {g₁ : Grade} {a : ObjTy} {g₂ : Grade}
    (condition : Expr .bool)
    (yes : Tree g₁ a)
    (no : Tree g₂ a) :
    Tree (g₁.join g₂) a :=
  private_decl% ⟨.branch condition yes.rep no.rep⟩

public def matchMany {types : List ObjTy} {a : ObjTy} {grade : Grade} {grades : List Grade}
    (values : Args Expr types) (rows : Rows types a (grade :: grades)) :
    Tree (Grade.joins (grade :: grades)) a :=
  private_decl% ⟨.matchMany values rows.rep⟩

public def «scoped» {g : Grade} (scope : Execute.Scope Expr) (body : Tree g .i32) :
    Tree (scope.grade g) .unit := private_decl% ⟨.scoped scope body.rep⟩

/-- Explicit grade subsumption retains the program and records its declared upper bound. -/
public def weaken {g h : Grade} {a : ObjTy} (tree : Tree g a) (included : g.Below h) : Tree h a :=
  private_decl% ⟨.weaken included tree.rep⟩

private def bindLocal
    {a : ObjTy} {g₁ : Grade} {g₂ : Grade} {b : ObjTy}
    (name : Local a)
    (value : Tree g₁ a)
    (body : Tree g₂ b) :
    Tree (g₁.seq g₂) b :=
  ⟨.bind name value.rep body.rep⟩

end Tree

end Oria.IR.Tree
