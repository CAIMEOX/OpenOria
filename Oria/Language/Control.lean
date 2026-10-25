module

public import Oria.Language.Builder
public import Oria.Language.Failure
import all Oria.Language.Builder
import all Oria.Data.Sealed

namespace Oria.Control.Internal

universe u

/-- Compiler carrier for one lexical object return destination. -/
public structure Target (A : Type) (r : Region) {a : ObjTy} [Object A a] where
  private mk ::
  private key : Sealed (A, r) (IR.Local a)

/-- Quote a block with a fresh return destination. Used by the do elaborator. -/
public def block {g : Grade} {A : Type} {r : Region} {a : ObjTy} [Object A a]
    (body : Target A r → Prog g A r) : Prog g A r :=
  private_decl% makeProg <| IR.Tree.Build.block fun key => (body ⟨Sealed.mk key⟩).quote

/-- Exit a lexical block while retaining the current continuation's local result type. -/
public def leave {A B : Type} {r q : Region} {a b : ObjTy} [Object A a] [Object B b]
    (target : Target A r) (value : Val A r) : Prog .pure B q :=
  private_decl% makeProg (pure (.leave target.key.get (reveal value)))

/-- Stage a finite host list with one declared grade bound for all iterations. -/
public def forList {g : Grade} {A : Type u} (values : List A) (body : A → Prog g Unit) : Prog g Unit :=
  values.foldr (fun x next => by simpa using Prog.bind (body x) (fun _ => next))
    ((Prog.pure Val.unit).weaken (Grade.pure_below g))

end Oria.Control.Internal
