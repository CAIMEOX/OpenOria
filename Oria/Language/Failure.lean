module

public import Oria.Language.Builder
import all Oria.Language.Builder

namespace Oria.Prog

/-- Leave through the recoverable failure exit. No normal value is produced. -/
public def fail {A : Type} {a : ObjTy} {r : Region} [Object A a] : Prog .failure A r :=
  private_decl% makeProg (Pure.pure IR.Tree.Tree.fail)

/-- Recover from failure in the body. Handler failure propagates to the enclosing scope. -/
public def catchFailure {g h : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (body : Prog g A r) (handler : Prog h A r) : Prog (g.handled.seq h) A r :=
  private_decl% makeProg (IR.Tree.Tree.catching <$> body.quote <*> handler.quote)

/-- Transform a normal result; failure and earlier effects are preserved. -/
public def map {g : Grade} {A B : Type} {a b : ObjTy} {r q : Region}
    [Object A a] [Object B b] (f : Val A r → Val B q) (p : Prog g A r) : Prog g B q := by
  simpa using bind p (fun v => pure (f v))

/-- Execute once, ignore recoverable failure, and discard the normal result. -/
public def ignore {g : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (p : Prog g A r) : Prog g.handled Unit := by
  simpa using catchFailure p.discard (pure Val.unit)

/-- Recover with a normal fallback value. -/
public def getD {g : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (p : Prog g A r) (fallback : Val A r) : Prog g.handled A r := by
  simpa using catchFailure p (pure fallback)

/-- Execute the fallback once if the first computation fails. -/
public def orElse {g h : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (p : Prog g A r) (fallback : Prog h A r) : Prog (g.handled.seq h) A r :=
  catchFailure p fallback

/-- Capture completion as ordinary object data. Earlier effects remain observable. -/
public def attempt {g : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (p : Prog g A r) : Prog g.handled (Option A) := by
  simpa using catchFailure (bind p (fun v => Oria.Option.some (v : Val A))) Oria.Option.none

/-- Observe whether the computation completes normally, without retaining its payload. -/
public def isSuccess {g : Grade} {A : Type} {a : ObjTy} {r : Region} [Object A a]
    (p : Prog g A r) : Prog g.handled Bool := by
  simpa using catchFailure (map (fun _ => Bool.lit true) p) (pure (Bool.lit false))

end Oria.Prog
