module

public import Oria.Runtime.Config
public import Oria.IR.Representation.Persistent
public import Oria.IR.Tree.Elaborated
import Oria
import all Oria.Language.Builder

namespace Oria.Runtime.GC

open Oria.Std Oria.Std.Command.Arg
open Oria.Representation.Persistent

@[expose] public def grade : Grade :=
  ⟨Req.none, Eff.world ||| Eff.scoreboardRead ||| Eff.scoreboardWrite ||| Eff.random ||| Eff.failure⟩

private theorem storageBelow (storage : ResourceId) (req : ReqRow := Req.none)
    (empty : req = Req.none := by rfl) (handled : Bool := false) :
    (if handled then (Data.grade (.storage storage) req).handled else Data.grade (.storage storage) req).Below grade := by
  subst req
  simp only [Data.grade, DataTarget.storage_requirements, Req.none, BitVec.zero_or]
  cases handled <;> decide

private def todo : Nbt.Path Scalar (Nbt.Value .compound) := .key "gc_todo"
private def object : Nbt.Path Scalar (Nbt.Value .compound) := .key "gc_object"
private def slot (index : Val Int32) : Nbt.Path Scalar (Nbt.Value .compound) :=
  (Nbt.Path.key "slots").at (.dynamic index)

private def panic (c : Config) : Prog grade Int32 :=
  (Prog.bind (Scoreboard.set (.named "#panic") c.objective (.static 1)).ignore
    (fun _ => Prog.fail (A := Int32))).weaken

/-- A missing required field is corruption; an empty worklist is handled separately. -/
private def require (c : Config) (action : Prog grade Int32) : Prog grade Int32 := do
  try
    action
  catch _ =>
    panic c

private def get (c : Config) (storage : ResourceId) (path : Nbt.Path Scalar (Nbt.Value .compound)) : Prog grade Int32 :=
  require c ((Data.get (.storage storage) (some path)).weaken (storageBelow storage))

/-- Writes are idempotent; native 'unchanged' does not indicate corruption. -/
private def put (storage : ResourceId) (path : Nbt.Path Scalar (Nbt.Value .compound)) (value : Val Int32) : Prog grade Unit :=
  (Data.modify (.storage storage) path .set (.value (.hole .i32 value))).ignore.weaken
    (storageBelow storage _ (by simp) true)

private def copy (target : ResourceId) (path : Nbt.Path Scalar (Nbt.Value .compound))
    (source : ResourceId) (sourcePath : Nbt.Path Scalar (Nbt.Value .compound)) : Prog grade Unit :=
  (Data.modify (.storage target) path .set (.from (.storage source) (some sourcePath))).ignore.weaken
    (storageBelow target _ (by simp) true)

private def append (c : Config) (storage : ResourceId) (path : Nbt.Path Scalar (Nbt.Value .compound)) : Prog grade Int32 :=
  require c ((Data.modify (.storage c.runtime) todo .append (.from (.storage storage) (some path))).weaken
    (storageBelow c.runtime _ (by simp)))

private def putBit (storage : ResourceId) (path : Nbt.Path Scalar (Nbt.Value .compound)) (bit : Val Int32) : Prog grade Unit :=
  (Prog.branch (bit == 0)
    (Data.modify (.storage storage) path .set (.ofNbt (0 : Int32))).ignore
    (Data.modify (.storage storage) path .set (.ofNbt (1 : Int32))).ignore).weaken (by
      simp only [DataSource.ofNbt_requirements, Grade.join_idem]
      exact storageBelow storage (handled := true))

private def unlink (c : Config) (previous : Val Int32) : Prog grade Unit := do
  if previous == 0 then copy c.storage (.key "used") c.runtime (object.field "next")
  else
    let index := previous - 1
    copy c.storage ((slot index).field "next") c.runtime (object.field "next")

/-- Scan static scratch offsets after one whole-object fetch. -/
private def scan (c : Config) (scanner : Scanner) : Prog grade Int32 :=
  let offsets := (List.finRange scanner.slots).filterMap fun i =>
    match scanner.layout.payload.get i with
    | .scalar => none
    | .pointer _ => some i.val
  offsets.foldr (fun i rest => do
    let path := (object.field "payload").at (.static (Int32.ofNat i))
    let child ← get c c.runtime path
    Prog.branch (child > 0) (append c c.runtime path)
      ((Prog.pure (0 : Val Int32)).weaken (h := grade))
    rest) ((Prog.pure (0 : Val Int32)).weaken)

private def dispatch (c : Config) (scanners : Array Scanner) (descriptor : Val Int32) :
    Prog grade Int32 :=
  scanners.toList.foldr (fun scanner rest => do
    if descriptor == Int32.ofNat scanner.code then scan c scanner
    else rest) (panic c)

private def mark (c : Config) (scanners : Array Scanner) (epoch : Val Int32) :
    Prog grade Int32 :=
  Prog.fix fun again => do
    let pointer ← ((Data.get (.storage c.runtime) (some (todo.at (.static (-1))))).getD (-1)).weaken
      (storageBelow c.runtime (handled := true))
    if pointer < 0 then return 0
    else
      (Data.remove (.storage c.runtime) (todo.at (.static (-1)))).ignore
      if pointer == 0 then again
      else
        let index := pointer - 1
        get c c.storage (slot index)
        copy c.runtime object c.storage (slot index)
        let descriptor ← get c c.runtime (object.field "d")
        let marked ← get c c.runtime (object.field "mark")
        if descriptor <= 0 then panic c
        else
          if marked == epoch then again
          else
            putBit c.storage ((slot index).field "mark") epoch
            dispatch c scanners descriptor
            again

private def sweep (c : Config) (epoch : Val Int32) :
    Val Int32 → Val Int32 → Prog grade Int32 :=
  Prog.fix fun again current previous => do
    if current <= 0 then return 0
    else
      let index := current - 1
      copy c.runtime object c.storage (slot index)
      let next ← get c c.runtime (object.field "next")
      let marked ← get c c.runtime (object.field "mark")
      if marked == epoch then again next current
      else
        unlink c previous
        (Data.modify (.storage c.storage) (slot index) .set (.ofNbt (nbt% {d: 0}))).ignore
        copy c.storage ((slot index).field "next") c.storage (.key "free")
        put c.storage (.key "free") current
        again next previous

private def body (c : Config) (scanners : Array Scanner) (roots : Array (ResourceId × Nat)) :
    Prog grade Int32 := do
  let old ← get c c.storage (.key "epoch")
  let epoch := 1 - old
  (Data.modify (.storage c.runtime) todo .set (.ofNbt (nbt% []))).ignore
  roots.toList.foldr (fun (id, offset) rest => do
    append c c.storage (((Nbt.Path.key "roots").field id.text).at (.static (Int32.ofNat offset)))
    rest) ((Prog.pure (0 : Val Int32)).weaken (h := grade))
  mark c scanners epoch
  let first ← get c c.storage (.key "used")
  sweep c epoch first 0
  putBit c.storage (.key "epoch") epoch
  return 0

private def collect (c : Config) (scanners : Array Scanner) (roots : Array (ResourceId × Nat)) : Prog grade.handled Unit := do
  (body c scanners roots).ignore
  (Data.remove (.storage c.runtime) todo).ignore
  (Data.remove (.storage c.runtime) object).ignore

/-- The collector is an internal unit-returning definition, invoked only by maintenance entries. -/
public def reference : IR.DeclRef ⟨[], .unit, grade.handled⟩ := .named ``collect

/-- Instantiate the runtime library through the existing sealed compiler capture. -/
public def generate (c : Config) (scanners : Array Scanner) (roots : Array (ResourceId × Nat)) : ElaboratedDef :=
  private_decl% (McFunction.Internal.capture ``collect (collect c scanners roots)).compile

end Oria.Runtime.GC
