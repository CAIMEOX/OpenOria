module

public import Oria.Datapack.Artifact
import all Oria.Meta.Datapack
import all Oria.Meta.Datapack.Eval
import Lean.Meta.Eval
import Lake.Util.IO

namespace Oria.Datapack

open Lean System

private def moduleArtifacts (moduleName : Name) : MetaM (Array (Name × Artifact)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? moduleName
    | throwError "module `{moduleName}` is not imported"
  Elab.datapackAttribute.ext.getModuleEntries env idx |>.mapM fun decl => do
    let artifact ← Eval.artifact (mkConst (decl ++ `artifact))
    pure (privateToUserName decl, artifact)

/-- Export every checked datapack declared in a compiled module. Each pack uses its source
name as a subdirectory. The file inventory owns generated files across incremental builds;
other files in the destination are preserved. Lean's search path must already be initialized. -/
public def exportModule (moduleName : Name) (destination : FilePath) : IO Unit := do
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[{module := moduleName, importAll := true}] {}
    (loadExts := true) (leakEnv := true)
  let artifacts ← Prod.fst <$> Lean.Meta.MetaM.toIO (moduleArtifacts moduleName)
    {fileName := moduleName.toString, fileMap := default, maxHeartbeats := 0}
    {env} {} {}
  let inventory := destination / "manifest.json"
  let previous : Array FilePath ← if ← inventory.pathExists then do
    let result := Json.parse (← IO.FS.readFile inventory) >>= fromJson?
    IO.ofExcept result
  else pure #[]
  let files := artifacts.flatMap fun (name, artifact) =>
    artifact.files.map fun file => {file with path := name.toString / file.path}
  let current := files.foldl (fun paths file => paths.insert file.path)
    ({} : Std.HashSet FilePath)
  for file in files do
    let path := destination / file.path
    Lake.createParentDirs path
    IO.FS.writeFile path file.contents
  for path in previous do
    unless current.contains path do Lake.removeFileIfExists (destination / path)
  Lake.createParentDirs inventory
  IO.FS.writeFile inventory ((toJson (files.map (·.path))).pretty 120 ++ "\n")

end Oria.Datapack
