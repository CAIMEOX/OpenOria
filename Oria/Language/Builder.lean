module

public import Oria.IR.Tree.Definition
public import Oria.Language.Object.Type
public import Oria.Language.Region
public import Oria.IR.Tree.Elaborated
public import Oria.Data.Sealed
import all Oria.IR.Tree.Elaborated
import all Oria.Data.Sealed

namespace Oria

universe u

open IR

/-- A staged object value indexed by its Lean source type. -/
public structure Val
    (A : Type) (r : Region := .any) {a : ObjTy} [Object A a] where
  private mk ::
  private representation : Sealed (A, r) (IR.Tree.Expr a)

set_option backward.privateInPublic true in
private opaque Val.expr {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (value : Val A r) : IR.Tree.Expr a := value.representation.get

/-- A graded object computation that quotes directly to structured Tree. -/
public structure Prog
    (g : Grade) (A : Type) (r : Region := .any) {a : ObjTy} [Object A a] where
  private mk ::
  private representation : Sealed (A, r) (IR.Tree.Build (IR.Tree.Tree g a))

private def Prog.quote {g : Grade} {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (program : Prog g A r) : IR.Tree.Build (IR.Tree.Tree g a) := program.representation.get

/-- A command hole whose Tree expression is fixed while its source type remains hidden. -/
public structure EncodedVal (a : ObjTy) where
  private mk ::
  private representation : Sealed a (IR.Tree.Expr a)

private def EncodedVal.expr {a : ObjTy} (value : EncodedVal a) : IR.Tree.Expr a :=
  value.representation.get

namespace McFunction.Internal

/-- Inert compiler carrier. Its representation and eliminator are not public. -/
public structure Recipe where
  private mk ::
  private representation : Sealed () ElaboratedDef

end McFunction.Internal

/-- Internal interpreter for a curried source function over one parameter telescope. -/
public class BuildFn (F : Type u) (sig : outParam Signature) where
  private mk ::
  private implementation : Sealed (F, sig)
    ((F → Args IR.Tree.Expr sig.args → IR.Tree.Build (IR.Tree.Tree sig.grade sig.result)) ×
      ((Args IR.Tree.Expr sig.args → IR.Tree.Build (IR.Tree.Tree sig.grade sig.result)) → F))

set_option backward.privateInPublic true in
private opaque BuildFn.lower {F : Type u} {sig : Signature} (fn : BuildFn F sig) :
    F → Args IR.Tree.Expr sig.args → IR.Tree.Build (IR.Tree.Tree sig.grade sig.result) :=
  (Sealed.get fn.implementation).1

set_option backward.privateInPublic true in
private opaque BuildFn.reify {F : Type u} {sig : Signature} (fn : BuildFn F sig) :
    (Args IR.Tree.Expr sig.args → IR.Tree.Build (IR.Tree.Tree sig.grade sig.result)) → F :=
  (Sealed.get fn.implementation).2

set_option backward.privateInPublic true in
private opaque makeVal {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (expr : IR.Tree.Expr a) : Val A r :=
  ⟨Sealed.mk expr⟩

set_option backward.privateInPublic true in
private opaque makeProg {g : Grade} {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (quote : IR.Tree.Build (IR.Tree.Tree g a)) : Prog g A r :=
  ⟨Sealed.mk quote⟩

private def makeEncodedVal {a : ObjTy} (expr : IR.Tree.Expr a) : EncodedVal a :=
  ⟨Sealed.mk expr⟩

private def makeRecipe (elaborated : ElaboratedDef) : McFunction.Internal.Recipe :=
  ⟨Sealed.mk elaborated⟩

@[implicit_reducible] private def makeBuildFn {F : Type u} {sig : Signature}
    (lower :
      F →
      Args IR.Tree.Expr sig.args →
      IR.Tree.Build (IR.Tree.Tree sig.grade sig.result))
    (reify : (Args IR.Tree.Expr sig.args → IR.Tree.Build (IR.Tree.Tree sig.grade sig.result)) → F) :
    BuildFn F sig :=
  ⟨Sealed.mk (lower, reify)⟩

private def ofExpr {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (expr : IR.Tree.Expr a) : Val A r :=
  makeVal expr

private def reveal {A : Type} {r : Region} {a : ObjTy} {object : Object A a}
    (value : @Val A r a object) : IR.Tree.Expr a :=
  value.expr

private def revealEncoded {a : ObjTy} (value : EncodedVal a) : IR.Tree.Expr a :=
  value.expr


public instance {A : Type} {r : Region} {a : ObjTy} {object : Object A a}
    (value : @Val A r a object) :
    CoeDep (@Val A r a object) value (EncodedVal a) where
  coe := private makeEncodedVal value.expr

/-- Forget a region guarantee while retaining the same object expression. -/
public instance {A : Type} {r : Region} {a : ObjTy} {object : Object A a} :
    CoeHead (@Val A r a object) (@Val A .any a object) where
  coe value := private makeVal value.expr

/-- Forget only the result guarantee, preserving the computation and its grade. -/
public instance {g : Grade} {A : Type} {r : Region} {a : ObjTy} {object : Object A a} :
    CoeHead (@Prog g A r a object) (@Prog g A .any a object) where
  coe program := private makeProg program.quote

private def revealRequest {route : Command.Signature}
    (request : Command.Call EncodedVal route) :
    Command.Call IR.Tree.Expr route :=
  request.map revealEncoded

private def perform {A : Type} {r : Region} {g : Grade} {a : ObjTy}
    [Object A a] (primitive : IR.Tree.Prim g a) : Prog g A r :=
  makeProg (pure (.perform primitive))

namespace Prog

public def weaken {g h : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (program : Prog g A r) (included : g.Below h := by decide) : Prog h A r :=
  makeProg (Functor.map (fun tree => tree.weaken included) program.quote)

public def pure {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (value : Val A r) : Prog .pure A r :=
  makeProg (Pure.pure (IR.Tree.Tree.ret (reveal value)))

public def bind
    {g₁ g₂ : Grade}
    {A B : Type} {a b : ObjTy}
    {r q : Region}
    [Object A a] [Object B b]
    (program : Prog g₁ A r)
    (next : Val A r → Prog g₂ B q) :
    Prog (g₁.seq g₂) B q :=
  makeProg do
    let value ← program.quote
    IR.Tree.Build.bind value fun expression =>
      (next (ofExpr expression)).quote

/-- Execute a computation and retain its grade while discarding its logical result. -/
public def discard {g : Grade} {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (program : Prog g A r) : Prog g Unit :=
  makeProg <| (Grade.seq_pure g) ▸ (do
    let value ← program.quote
    IR.Tree.Build.bind value fun _ =>
      Pure.pure (IR.Tree.Tree.ret (.unit : IR.Tree.Expr .unit)))

public def branch
    {g₁ g₂ : Grade}
    {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (condition : Val Bool)
    (yes : Prog g₁ A r)
    (no : Prog g₂ A r) :
    Prog (g₁.join g₂) A r :=
  makeProg do
    let yes ← yes.quote
    let no ← no.quote
    Pure.pure (IR.Tree.Tree.branch (reveal condition) yes no)

end Prog

namespace Task

/-- Permit the runtime to park this computation when the current slice has insufficient fuel. -/
public def checkpoint : Prog .suspension Unit := perform (.checkpoint false)

/-- Continue this computation on the next game tick. -/
public def «yield» : Prog .suspension Unit := perform (.checkpoint true)

end Task

namespace Command

/-- Execute a native command; failure uses the computation's failure exit. -/
public def emit
    {route : Command.Signature}
    (request : Call EncodedVal route) :
    Prog request.grade Int32 := by
  simpa [revealRequest] using
    (perform (.command (revealRequest request)) : Prog _ Int32)

end Command

namespace Execute

/-- Run a Unit- or Int32-returning body per selected context. Failure stops that branch;
normal Unit completion supplies result zero. Lexical captures are retained. -/
public def forEach {g : Grade} {A : Type} {a : ObjTy} [Object A a]
    (steps : List (Step EncodedVal)) (body : Prog g A)
    (_supported : a = .unit ∨ a = .i32 := by first | exact Or.inl rfl | exact Or.inr rfl)
    (_synchronous : g.canSuspend = false := by decide) :
    Prog ((Scope.ofSteps steps).grade g) Unit :=
  makeProg do
    let tree ← body.quote
    let body ← IR.Tree.Build.bind tree fun value =>
      Pure.pure (IR.Tree.Tree.ret (if h : a = .i32 then h ▸ value else .i32 0))
    pure (IR.Tree.Tree.scoped ((Scope.ofSteps steps).map revealEncoded)
      ((Grade.seq_pure g) ▸ body))

end Execute

namespace Option

public def none {A : Type} {a : ObjTy} [Object A a] : Prog .pure (Option A) :=
  perform (.construct .none .nil)

public def some {A : Type} {a : ObjTy} {object : Object A a}
    (value : @Val A .any a object) : Prog .pure (Option A) :=
  perform (.construct .some (.cons (reveal value) .nil))

/-- Eliminate an Option while binding its payload only in the success branch. -/
public def elim
    {noneGrade someGrade : Grade}
    {A B : Type} {a b : ObjTy} {r q : Region}
    [Object A a] [Object B b]
    (scrutinee : Val (Option A) r)
    (noneBranch : Prog noneGrade B q)
    (someBranch : Val A r → Prog someGrade B q) :
    Prog (noneGrade.join someGrade) B q :=
  makeProg do
    let noneBody ← noneBranch.quote
    IR.Tree.Build.caseUnary .none .some (reveal scrutinee) noneBody fun payload =>
      (someBranch (ofExpr payload)).quote

end Option


namespace Val

public def unit : Val Unit :=
  ofExpr .unit

end Val

namespace Bool

public def lit (value : Bool) : Val Bool :=
  ofExpr (.bool value)

public def not (value : Val Bool) : Val Bool := ofExpr (.unary .not (reveal value))

public def eq (left right : Val Bool) : Val Bool :=
  ofExpr (.binary .beq (reveal left) (reveal right))

public def and (left right : Val Bool) : Val Bool :=
  ofExpr (.ite (reveal left) (reveal right) (.bool false))

public def or (left right : Val Bool) : Val Bool :=
  ofExpr (.ite (reveal left) (.bool true) (reveal right))

end Bool

namespace I32

public def lit (value : Int32) : Val Int32 :=
  ofExpr (.i32 value)

public def neg {r : Region} (value : Val Int32 r) : Val Int32 :=
  ofExpr (.unary .neg (reveal value))

public def add {r q : Region} (left : Val Int32 r) (right : Val Int32 q) : Val Int32 :=
  ofExpr (.binary .add (reveal left) (reveal right))

public def sub {r q : Region} (left : Val Int32 r) (right : Val Int32 q) : Val Int32 :=
  ofExpr (.binary .sub (reveal left) (reveal right))

public def mul {r q : Region} (left : Val Int32 r) (right : Val Int32 q) : Val Int32 :=
  ofExpr (.binary .mul (reveal left) (reveal right))

/-- Native scoreboard division rounds down and exits through Failure on a zero divisor.
The signed overflow case wraps to `Int32.minValue`. -/
public def div {r q : Region} (left : Val Int32 r) (right : Val Int32 q) :
    Prog .failure Int32 :=
  perform (.division (reveal left) (reveal right))

public def le {r q : Region} (left : Val Int32 r) (right : Val Int32 q) : Val Bool :=
  ofExpr (.binary .le (reveal left) (reveal right))

public def lt (left right : Val Int32) : Val Bool :=
  ofExpr (.binary .lt (reveal left) (reveal right))

public def eq (left right : Val Int32) : Val Bool :=
  ofExpr (.binary .eq (reveal left) (reveal right))

end I32

public instance {r q : Region} : HAdd (Val Int32 r) (Val Int32 q) (Val Int32) where
  hAdd := I32.add

public instance {r q : Region} : HSub (Val Int32 r) (Val Int32 q) (Val Int32) where
  hSub := I32.sub

public instance {r q : Region} : HMul (Val Int32 r) (Val Int32 q) (Val Int32) where
  hMul := I32.mul

public instance {r q : Region} : HDiv (Val Int32 r) (Val Int32 q) (Prog .failure Int32) where
  hDiv := I32.div

public instance {r : Region} : HAdd (Val Int32 r) Nat (Val Int32) where
  hAdd v n := I32.add v (I32.lit (Int32.ofNat n))

public instance {r : Region} : HAdd Nat (Val Int32 r) (Val Int32) where
  hAdd n v := I32.add (I32.lit (Int32.ofNat n)) v

public instance {r : Region} : HSub (Val Int32 r) Nat (Val Int32) where
  hSub v n := I32.sub v (I32.lit (Int32.ofNat n))

public instance {r : Region} : HSub Nat (Val Int32 r) (Val Int32) where
  hSub n v := I32.sub (I32.lit (Int32.ofNat n)) v

public instance {r : Region} : HMul (Val Int32 r) Nat (Val Int32) where
  hMul v n := I32.mul v (I32.lit (Int32.ofNat n))

public instance {r : Region} : HMul Nat (Val Int32 r) (Val Int32) where
  hMul n v := I32.mul (I32.lit (Int32.ofNat n)) v

public instance {r : Region} : HDiv (Val Int32 r) Nat (Prog .failure Int32) where
  hDiv v n := I32.div v (I32.lit (Int32.ofNat n))

public instance {r : Region} : HDiv Nat (Val Int32 r) (Prog .failure Int32) where
  hDiv n v := I32.div (I32.lit (Int32.ofNat n)) v

public instance : Neg (Val Int32) where
  neg := I32.neg

public instance (n : Nat) : OfNat (Val Int32) n where
  ofNat := I32.lit (Int32.ofNat n)

public instance {A : Type} {r : Region} {a : ObjTy} {g : Grade} [Object A a] :
    BuildFn (Prog g A r) { args := [], result := a, grade := g } :=
  private_decl% (makeBuildFn (fun program arguments =>
    match arguments with
    | .nil => program.quote)
    (fun quote => makeProg (quote .nil)))

public instance {A : Type} {F : Type u} {r : Region} {a : ObjTy} {sig : Signature}
    [Object A a] [next : BuildFn F sig] :
    BuildFn (Val A r → F) { sig with args := a :: sig.args } :=
  private_decl% (makeBuildFn (fun build arguments =>
    match arguments with
    | .cons expression rest =>
        next.lower (build (ofExpr expression)) rest)
    (fun quote value => next.reify (fun rest => quote (.cons (reveal value) rest))))

/-- Region polymorphism changes source guarantees without adding an object argument. -/
public instance {F : Region → Type u} {sig : Signature}
    [next : ∀ r, BuildFn (F r) sig] : BuildFn ({r : Region} → F r) sig :=
  private_decl% (makeBuildFn (fun build args => (next .any).lower (build (r := .any)) args)
    (fun quote {r} => (next r).reify quote))

/-- Build one finite recursive definition over the source function's complete parameter telescope. -/
public def Prog.fix {g : Grade} {args : List ObjTy} {a : ObjTy} {F : Type u}
    [fn : BuildFn F ⟨args, a, g⟩] (body : F → F) : F :=
  fn.reify fun initial => IR.Tree.Build.fix
    (fun recur => fn.lower (body (fn.reify (fun values => Pure.pure (recur values))))) initial

namespace Builder

/-- Quote one accepted source builder directly to a structured Tree definition. -/
private def quoteDefinition
    {F : Type u} {sig : Signature}
    (source : Lean.Name)
    (build : F)
    [builder : BuildFn F sig] :
    ElaboratedDef :=
  ⟨source, sig, IR.Tree.Def.build (builder.lower build)⟩

end Builder

namespace McFunction.Internal

/-- Capture a builder in an inert value for the compiler attribute. -/
public def capture
    {F : Type u} {sig : Signature}
    (source : Lean.Name)
    (build : F)
    [BuildFn F sig] : Recipe :=
  makeRecipe (Builder.quoteDefinition source build)

private def Recipe.compile (recipe : Recipe) : ElaboratedDef :=
  recipe.representation.get

end McFunction.Internal

end Oria
