module

public import Oria.Datapack.Spec
meta import Oria.Datapack.Resource
public import Oria.IR.DP121.Program
import Oria.IR.DP121.Pretty
import Lean.Data.Json.FromToJson.Basic
public import Lean.ToExpr
import Lean.Elab.Deriving.ToExpr

namespace Oria.Datapack

public structure File where
  path : System.FilePath
  contents : String
  deriving Lean.ToExpr

/-- Rendered files assembled by the compiler; writing is an explicit IO action. -/
public structure Artifact where
  private mk ::
  files : Array File
  deriving Lean.ToExpr

namespace Artifact

private def functionFile (id : FunctionId) (contents : String) : File :=
  let dir : System.FilePath := "data" / id.resourceNamespace.render / "function"
  let path := id.path.segments.foldl (· / ·) dir
  ⟨path.addExtension "mcfunction", contents ++ "\n"⟩

private def metadata (settings : Settings) : File :=
  let (major, minor) := settings.version.dataPackVersion
  let version := Lean.toJson [major, minor]
  let json := Lean.Json.mkObj [("pack", Lean.Json.mkObj [
    ("description", Lean.toJson settings.description),
    ("min_format", version), ("max_format", version)])]
  ⟨"pack.mcmeta", json.pretty 120 ++ "\n"⟩

private def tag (name : String) (target : FunctionId) : File :=
  let path : System.FilePath := "data" / "minecraft" / "tags" / "function" / name
  let json := Lean.Json.mkObj [
    ("replace", Lean.toJson false), ("values", Lean.toJson [target.render])]
  ⟨path.addExtension "json", json.pretty 120 ++ "\n"⟩

private def checkPaths (files : Array File) : Except Diagnostic Unit := do
  let mut paths : Std.HashSet System.FilePath := {}
  for file in files do
    if paths.contains file.path then throw (.artifactPathConflict file.path.toString)
    paths := paths.insert file.path
  for file in files do
    for parent in (file.path.components.scanl (· / ·) ("" : System.FilePath)).dropLast do
      if paths.contains parent then throw (.artifactPathConflict parent.toString)

/-- Assemble DP121 files after structured calls have been checked. -/
public def ofProgram (settings : Settings) (program : Target.DP121.Program)
    (_closed : program.Closed) : Except Diagnostic Artifact := do
  let files := program.functions.map fun ⟨_, definition⟩ =>
    functionFile definition.ref.id (definition.body.pretty 120)
  let load := FunctionId.ofParts settings.ns "__oria/load"
  let tick := FunctionId.ofParts settings.ns "__oria/tick"
  let plain (id : FunctionId) := program.functions.any fun
    | ⟨.plain, definition⟩ => definition.ref.id.render == id.render
    | ⟨.macro _, _⟩ => false
  unless plain load do throw (.unresolvedTargetFunction load.render)
  let files := files ++ #[metadata settings, tag "load" load]
  let files := if plain tick then files.push (tag "tick" tick) else files
  checkPaths files
  pure ⟨files.qsort fun a b => a.path.toString < b.path.toString⟩

/-- Write to a new or empty directory, preserving all existing nonempty destinations. -/
public def writeTo (artifact : Artifact) (destination : System.FilePath) : IO Unit := do
  if ← destination.pathExists then
    unless ← destination.isDir do
      throw (.userError s!"datapack destination is not a directory: {destination}")
    unless (← destination.readDir).isEmpty do
      throw (.userError s!"datapack destination must be empty: {destination}")
  IO.FS.createDirAll destination
  for file in artifact.files do
    let path := destination / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path file.contents

end Artifact

end Oria.Datapack
