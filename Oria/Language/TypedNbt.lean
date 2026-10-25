module

public import Oria.Language.Builder
public import Oria.Language.NbtGlobal
public import Oria.Nbt.Description
import all Oria.Language.Builder
import all Oria.Nbt.Description

namespace Oria.Nbt

open Oria.IR

/-- A schema-directed mutable location chosen while constructing the program.
Arena handles and registered globals share the same native operations. -/
public inductive Location (a : Type) [Repr a] where
  | arena : Val (Ref a) → Location a
  | global : Global a → Location a

/-- The receiver determines both the native content type and its representation.
Lean coercions require the target's dependent parameters first; output parameters here
also support root selections whose content type is inferred entirely from the receiver. -/
public class ToLocation (l : Type) (a : outParam Type) (r : outParam (Repr a)) where
  toLocation : l → @Location a r

public instance {a : Type} [r : Repr a] : ToLocation (Val (Ref a)) a r := ⟨.arena⟩
public instance {a : Type} [r : Repr a] : ToLocation (Global a) a r := ⟨.global⟩
public instance {a : Type} [r : Repr a] : ToLocation (Location a) a r := ⟨id⟩

/-- Native writes accept host values or object I32 values. -/
public inductive Source : (a : Type) → [Repr a] → Type 1 where
  | literal {a : Type} [Repr a] : a → Source a
  | i32 : Val Int32 → Source Int32

private def source : {a : Type} → {r : Repr a} → @Source a r → IR.Nbt.Write (EncodedVal .i32)
  | _, _, @Source.literal _ r value => .literal (@ToNbt.toNbt _ r.toToNbt value)
  | _, _, .i32 value => .i32 (value : EncodedVal .i32)

private def base {a : Type} [r : Repr a] : Location a →
    (as : List ObjTy) × IR.Nbt.Base as × Args EncodedVal as
  | .arena root => ⟨[.nbtRef r.schema], .arena .head, .cons (root : EncodedVal (.nbtRef r.schema)) .nil⟩
  | .global root => ⟨[], .global root.definition.ref, .nil⟩

/-- Capture the address and indices once, retaining their separate semantic roles. -/
private def selection {a b : Type} [Repr a] [r : Repr b]
    (root : Location a) (p : Access (Val Int32) a b) :
    (as : List ObjTy) × IR.Nbt.Base as × IR.Nbt.Path (Scope.Var Unit as .i32) × Args EncodedVal as :=
  let p := (IR.Nbt.Path.ofSegments r.schema (Access.raw p)).map
    (fun (v : Val Int32) => (v : EncodedVal .i32))
  let ⟨as, root, xs⟩ := base root
  let ⟨bs, p, ys⟩ := IR.Nbt.abstractPath p
  ⟨as ++ bs, root.rename (Scope.Renaming.appendLeft Unit as bs),
    p.map (fun x => x.weakenMany as), xs.append ys⟩

@[inline] private def measureValue {t : Option Tag} {r : Region}
    (value : Val (Data t) r) (suffix : Command.Fragment EncodedVal) (numeric : Bool) : Prog .failure Int32 :=
  match IR.Nbt.abstractFragment suffix with
  | ⟨as, p, values⟩ => by
      let op : IR.Nbt.Op (.nbt t :: as) .i32 :=
        .inspectValue .head (p.map (fun x => x.weaken (.nbt t))) numeric
      simpa only [op, IR.Nbt.Op.grade] using
        (perform (.memory (.nbt op) (.cons (reveal value) (values.map revealEncoded))) : Prog op.grade Int32)

/-- Allocate an owned native document in the logical invocation's arena. -/
public def alloc {a : Type} [r : Repr a] (value : a) : Prog IR.Nbt.writeGrade (Ref a) :=
  private_decl% perform (.memory (.nbt (.newRef r.schema (ToNbt.toNbt value))) .nil)

/-- Copy one typed selection into an immutable invocation-local snapshot. Later writes
leave it unchanged. A missing selection uses Failure; the snapshot may be persisted. -/
public def snapshot {l a b : Type} [r : Repr a] [Repr b] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a b) : Prog IR.Nbt.readGrade (Data none) :=
  private_decl% (match selection (ToLocation.toLocation root) p with
  | ⟨_, root, p, values⟩ =>
      perform (.memory (.nbt (.read .one (.reference root p))) (values.map revealEncoded)))

private def inspect {a b : Type} [Repr a] [Repr b]
    (root : Location a) (p : Access (Val Int32) a b) (numeric : Bool) : Prog IR.Nbt.readGrade Int32 :=
  match selection root p with
  | ⟨_, root, p, values⟩ =>
      perform (.memory (.nbt (.inspectRef root p numeric)) (values.map revealEncoded))

/-- Read an I32 field or element directly into the scalar computation domain. -/
public def readI32 {l a : Type} [r : Repr a] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a Int32) : Prog IR.Nbt.readGrade Int32 :=
  private_decl% inspect (ToLocation.toLocation root) p true

/-- Measure a native list without creating a snapshot. -/
public def length {l a b : Type} [r : Repr a] [Repr b] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a (Array b)) : Prog IR.Nbt.readGrade Int32 :=
  private_decl% inspect (ToLocation.toLocation root) p false

private def put {a b c : Type} [Repr a] [Repr b] [Repr c]
    (root : Location a) (p : Access (Val Int32) a b) (value : Source c) (append : Bool) :
    Prog IR.Nbt.writeGrade Unit :=
  match selection root p, IR.Nbt.abstractWrite (source value) with
  | ⟨as, root, p, xs⟩, ⟨bs, value, ys⟩ =>
      let ρ := Scope.Renaming.appendLeft Unit as bs
      let op := IR.Nbt.Op.putRef (root.rename ρ) (p.map (fun x => ρ x))
        (value.map (fun x => x.weakenMany as)) append
      perform (.memory (.nbt op) ((xs.append ys).map revealEncoded))

/-- Replace a typed selection using native `data modify ... set` semantics. An unchanged
value or an invalid list index uses Failure. Missing compound keys are created; negative
indices count from the end of a list. The native changed-target count is discarded. -/
public def set {l a b : Type} [r : Repr a] [Repr b] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a b) (value : Source b) : Prog IR.Nbt.writeGrade Unit :=
  private_decl% put (ToLocation.toLocation root) p value false

/-- Append one element to a typed native list. -/
public def append {l a b : Type} [r : Repr a] [Repr b] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a (Array b)) (value : Source b) : Prog IR.Nbt.writeGrade Unit :=
  private_decl% put (ToLocation.toLocation root) p value true

/-- Replace a typed native list with the empty list. An already empty list uses Failure.
Missing compound keys are created according to native `data modify ... set` semantics. -/
public def clear {l a b : Type} [r : Repr a] [Repr b] [ToLocation l a r]
    (root : l) (p : Access (Val Int32) a (Array b)) : Prog IR.Nbt.writeGrade Unit :=
  private_decl% (match selection (ToLocation.toLocation root) p with
  | ⟨_, root, p, values⟩ => perform (.memory (.nbt (.clearRef root p)) (values.map revealEncoded)))

private def transfer {a b c d : Type} [Repr a] [Repr b] [Repr c] [Repr d]
    (dst : Location a) (p : Access (Val Int32) a b)
    (src : Location c) (q : Access (Val Int32) c d) (append : Bool) : Prog IR.Nbt.copyGrade Unit :=
  match selection dst p, selection src q with
  | ⟨as, dst, p, xs⟩, ⟨bs, src, q, ys⟩ =>
      let left := Scope.Renaming.appendLeft Unit as bs
      let right := Scope.Renaming.appendRight Unit as bs
      let op := IR.Nbt.Op.copyRef (dst.rename left) (p.map (fun x => left x))
        (src.rename right) (q.map (fun x => right x)) append
      perform (.memory (.nbt op) ((xs.append ys).map revealEncoded))

/-- Copy equal-typed selections with native `data modify ... set from` semantics.
An unchanged destination, a missing source, or an invalid destination uses Failure.
Missing destination compound keys are created, and the changed-target count is discarded. -/
public def copy {l m a b c : Type} [r : Repr a] [Repr b] [s : Repr c]
    [ToLocation l a r] [ToLocation m c s]
    (dst : l) (p : Access (Val Int32) a b)
    (src : m) (q : Access (Val Int32) c b) : Prog IR.Nbt.copyGrade Unit :=
  private_decl% transfer (ToLocation.toLocation dst) p (ToLocation.toLocation src) q false

/-- Append one selected native value to a list with the same element type. -/
public def appendFrom {l m a b c : Type} [r : Repr a] [Repr b] [s : Repr c]
    [ToLocation l a r] [ToLocation m c s]
    (dst : l) (p : Access (Val Int32) a (Array b))
    (src : m) (q : Access (Val Int32) c b) : Prog IR.Nbt.copyGrade Unit :=
  private_decl% transfer (ToLocation.toLocation dst) p (ToLocation.toLocation src) q true

@[inline] private def exportTo {a b : Type} [Repr a] [Repr b]
    (root : Location a) (p : Access (Val Int32) a b)
    (target suffix : Command.Fragment EncodedVal) :
    Prog ⟨target.requirements ||| suffix.requirements,
      Eff.memoryRead ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩ Unit :=
  match selection root p, IR.Nbt.abstractFragment target, IR.Nbt.abstractFragment suffix with
  | ⟨as, root, p, xs⟩, ⟨bs, t, ys⟩, ⟨cs, q, zs⟩ => by
      let ρ := Scope.Renaming.appendLeft Unit as (bs ++ cs)
      let t := { t.map (fun x => (Scope.Renaming.appendLeft Unit bs cs x).weakenMany as)
          with requirements := target.requirements }
      let q := { q.map (fun x => (x.weakenMany bs).weakenMany as)
          with requirements := suffix.requirements }
      let op : IR.Nbt.Op (as ++ (bs ++ cs)) .unit :=
        .exportRef (root.rename ρ) (p.map (fun x => ρ x)) t q
      simpa only [op, IR.Nbt.Op.grade, t, q] using
        (perform (.memory (.nbt op) ((xs.append (ys.append zs)).map revealEncoded)) : Prog op.grade Unit)

end Oria.Nbt
