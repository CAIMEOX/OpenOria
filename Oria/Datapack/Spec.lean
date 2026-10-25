module

public import Oria.Datapack.Resource
public import Oria.Datapack.Version
public import Oria.IR.Common.Reference
public import Oria.Command.Argument
public import Oria.Language.Persistent
public import Oria.Language.NbtGlobal
import all Oria.Language.Persistent
import Std.Data.TreeSet.Basic
import Std.Data.HashSet.Basic

namespace Oria.Datapack

/-- The two automatically scheduled phases of one data pack. -/
public inductive Hook where
  | load
  | tick
  deriving BEq, DecidableEq, Repr

public inductive Registration where
  | entry {g : Grade} (path : PublicFunctionPath) (ref : IR.DeclRef ⟨[], .unit, g⟩)
  | hook {g : Grade} (phase : Hook) (ref : IR.DeclRef ⟨[], .unit, g⟩)
      (available : g.req ||| Req.server = Req.server)
  | task {g : Grade} (path : PublicFunctionPath) (ref : IR.DeclRef ⟨[], .unit, g⟩)
      (available : g.req ||| Req.server = Req.server)

namespace Registration

@[expose] public def reference : Registration → IR.DeclRef.Some
  | .entry _ ref | .hook _ ref _ | .task _ ref _ => ⟨_, ref⟩

@[expose] public def publicPath : Registration → Option PublicFunctionPath
  | .entry path _ | .task path _ _ => some path
  | .hook _ _ _ => none

public theorem arguments_empty (r : Registration) : r.reference.sig.args = [] := by
  cases r <;> rfl

public theorem result_unit (r : Registration) : r.reference.sig.result = .unit := by
  cases r <;> rfl

public theorem hook_requirements {g : Grade} (h : Hook)
    (ref : IR.DeclRef ⟨[], .unit, g⟩) (available : g.req ||| Req.server = Req.server) :
    (Registration.hook h ref available).reference.sig.grade.req ||| Req.server = Req.server := available

end Registration

public structure Settings where
  ns : ResourceNamespace
  description : String := ""
  version : Version := .dp121
  commands : Option (List Oria.Command.Decl) := none
  objective : Option Oria.Command.Objective := none
  registerBudget : Nat := 128
  sliceBudget : Nat := 20000

public structure Spec where
  settings : Settings
  registrations : Array Registration := #[]
  persistentRoots : Array (ResourceId × IR.RootRef.Some) := #[]
  globals : Array IR.Nbt.GlobalDecl := #[]
  collectors : Array PublicFunctionPath := #[]

public abbrev Builder := StateM Spec

public def entry {g : Grade} (path : PublicFunctionPath) (ref : IR.DeclRef ⟨[], .unit, g⟩) :
    Builder Unit := modify fun spec =>
  { spec with registrations := spec.registrations.push (.entry path ref) }

/-- Launch one server-context task and resume it in bounded slices on subsequent game ticks. -/
public def task {g : Grade} (path : PublicFunctionPath) (ref : IR.DeclRef ⟨[], .unit, g⟩)
    (available : g.req ||| Req.server = Req.server := by native_decide) : Builder Unit :=
  modify fun spec => { spec with registrations := spec.registrations.push (.task path ref available) }

public def onLoad {g : Grade} (ref : IR.DeclRef ⟨[], .unit, g⟩)
    (available : g.req ||| Req.server = Req.server := by native_decide) : Builder Unit :=
  modify fun spec => { spec with registrations := spec.registrations.push (.hook .load ref available) }

public def onTick {g : Grade} (ref : IR.DeclRef ⟨[], .unit, g⟩)
    (available : g.req ||| Req.server = Req.server := by native_decide) : Builder Unit :=
  modify fun spec => { spec with registrations := spec.registrations.push (.hook .tick ref available) }

/-- Register a source root under one stable persistent storage identity. -/
public def root {A : Type} {a : ObjTy} [Object A a]
    (id : ResourceId) (value : Persistent.Root A) : Builder Unit :=
  private_decl% modify fun spec =>
    { spec with persistentRoots := spec.persistentRoots.push (id, ⟨a, value.ref⟩) }

/-- Register an owned native subtree and its first-load initializer. The storage name is
relative to this datapack's namespace; runtime and persistent storage names are reserved. -/
public def global {a : Type} [Nbt.Repr a] (value : Nbt.Global a) : Builder Unit :=
  private_decl% modify fun spec => { spec with globals := spec.globals.push value.definition }

/-- Export a maintenance entry that runs after the ordinary invocation has returned. -/
public def collector (path : PublicFunctionPath) : Builder Unit :=
  modify fun spec => { spec with collectors := spec.collectors.push path }

public def build (settings : Settings) (body : Builder Unit) : Spec :=
  (body.run { settings }).2

namespace Spec

public def roots (spec : Spec) : Array IR.DeclRef.Some :=
  spec.registrations.map Registration.reference

/-- Diagnose export collisions while preserving the registration sequence. -/
public def check (spec : Spec) : Except Diagnostic Unit := do
  if spec.settings.registerBudget < 6 then
    throw (.invalidRegisterBudget spec.settings.registerBudget)
  let mut paths : Std.TreeSet PublicFunctionPath := {}
  for r in spec.registrations do
    if let some path := r.publicPath then
      if paths.contains path then throw (.duplicatePublicFunctionPath path.render)
      paths := paths.insert path
  for path in spec.collectors do
    if paths.contains path then throw (.duplicatePublicFunctionPath path.render)
    paths := paths.insert path
  let mut ids : Std.TreeSet String := {}
  let mut names : Std.HashSet Lean.Name := {}
  for (id, root) in spec.persistentRoots do
    unless id.text.startsWith (spec.settings.ns.render ++ ":") do
      throw (.invalidResourceId id.text)
    if ids.contains id.text || names.contains root.ref.name then
      throw (.duplicatePersistentRoot root.ref.name)
    ids := ids.insert id.text
    names := names.insert root.ref.name
  for (decl, i) in spec.globals.zipIdx do
    let root := decl.ref
    (Oria.Command.Literal.path root.path).check
    (Oria.Command.Literal.nbt decl.initial).check
    if root.storage.render == "runtime" || root.storage.render == "persistent" then
      throw (.reservedNbtGlobal root.storage.render)
    for decl in spec.globals.extract 0 i do
      let other := decl.ref
      let left := root.path.head :: root.path.tail
      let right := other.path.head :: other.path.tail
      if root.storage == other.storage && (left.isPrefixOf right || right.isPrefixOf left) then
        throw (.overlappingNbtGlobals root.storage.render)

end Spec

end Oria.Datapack
