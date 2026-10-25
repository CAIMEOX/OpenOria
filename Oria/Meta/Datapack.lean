module

public import Oria.Datapack.Artifact
public import Lean.Environment
import Oria.Meta.Collect
import Oria.Compiler
import Oria.Std.Manifest
import Oria.Runtime.GC
meta import all Oria.Meta.Datapack.Eval
import Qq.MetaM

namespace Oria.Datapack

/-- Compile an environment-backed data-pack specification to finite output files. -/
public def compile (env : Lean.Environment) (spec : Spec) : Except Diagnostic Artifact := do
  spec.check
  let settings := spec.settings
  let commands ← Oria.Command.Catalog.build
    (settings.commands.getD Std.Manifest.commandDeclarations)
  let objective ← match settings.objective with
    | some objective => pure objective
    | none => Oria.Command.Objective.parse (settings.ns.render ++ ".oria")
  let persistentRoots ← spec.persistentRoots.mapM fun (_, ref) => do
    let some root := PersistentRegistry.find? env ref.ref.name
      | throw (.unknownRoot ref.ref.name)
    unless root.initial.signature.result == ref.type do
      throw (.rootTypeMismatch ref.ref.name ref.type root.initial.signature.result)
    pure root
  let candidate ← Oria.collect env spec.roots commands persistentRoots
  for member in candidate.members do
    for root in member.dependencies.globals do
      unless spec.globals.any (fun declared => decide (declared.ref = root)) do
        throw (.unknownNbtGlobal root.storage.render (root.path.format.pretty 120))
  let prepared ← Lower.Machine.prepare candidate
  let config : Lower.DP121.Config := {
    resourceNamespace := settings.ns
    objective
    registerBudget := settings.registerBudget
    sliceBudget := settings.sliceBudget
    globals := spec.globals
    rootNames := Std.HashMap.ofList (spec.persistentRoots.toList.map fun (id, ref) => (ref.ref.name, id))
    collectors := spec.collectors.map fun path => ⟨Runtime.GC.grade.handled, path, Runtime.GC.reference⟩ }
  let candidate ← if spec.collectors.isEmpty then pure candidate else do
    let roots := spec.persistentRoots.flatMap fun (id, ref) =>
      (prepared.table.kinds ref.type).toArray.zipIdx.filterMap fun (word, offset) =>
        match word with
        | .pointer _ => some (id, offset)
        | .scalar => none
    let gc := Runtime.GC.generate (← config.memory) prepared.persistent.scanners roots
    Oria.includeRuntime env candidate #[gc]
  let collected ← candidate.checkClosure
  let compiled ← Oria.Program.compile collected
  let source := compiled.closed
  let machine ← Lower.Machine.lowerProgram source prepared
  let target ← Lower.DP121.lower config machine candidate.commands spec.registrations
  let ⟨closed⟩ ← target.checkCalls
  Artifact.ofProgram settings target closed

namespace Elab

open Lean Lean.Meta Lean.Elab.Command Qq

private def addDatapack (decl : Name) : CoreM Unit := do
  let attr ← getRef
  let env ← getEnv
  let artifactName := decl ++ `artifact
  if env.contains artifactName then
    throwErrorAt attr "generated datapack declaration `{artifactName}` already exists"
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwErrorAt attr "datapack declarations must have the closed type `Datapack.Spec`"
  let (_, staged) ← withoutModifyingEnv' do
    let spec ← MetaM.run' <| Eval.spec (mkConst decl)
    let artifact ← match compile env spec with
      | .ok artifact => pure artifact
      | .error diagnostic => throwErrorAt attr "datapack `{decl}`: {repr diagnostic}"
    addAndCompile (.defnDecl {
      name := artifactName
      levelParams := []
      type := q(Artifact)
      value := toExpr artifact
      hints := .opaque
      safety := .safe
    }) (logCompileErrors := true)
  setEnv staged

initialize datapackAttribute : TagAttribute ←
  registerTagAttribute `datapack
    "Compile a data-pack specification and publish its finite `.artifact`."
    (validate := fun decl => addDatapack decl)
    (applicationTime := .afterCompilation)

end Elab

end Oria.Datapack
