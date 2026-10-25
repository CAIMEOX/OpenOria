import Lake

open System Lean Lake DSL

package oria where
  version := v!"1.0.0"

require Qq from git
  "https://github.com/leanprover-community/quote4.git" @ "v4.31.0-rc2"

@[default_target]
lean_lib Oria
lean_lib OriaTests

lean_exe «oria-export» where
  root := `tools.Datapack
  supportInterpreter := true

/-- Export the datapacks declared by this module into its package's build directory. -/
module_facet datapack (mod) : FilePath := do
  let tool ← «oria-export».fetch
  let source ← mod.leanArts.fetch
  let destination := mod.pkg.buildDir / "datapacks" / mod.name.toString
  let inventory := destination / "manifest.json"
  tool.bindM fun exe => source.mapM fun _ => do
    let paths : Array FilePath ← if ← inventory.pathExists then do
      IO.ofExcept (Json.parse (← IO.FS.readFile inventory) >>= fromJson?)
    else pure #[]
    let missing ← paths.findM? fun path => return !(← (destination / path).pathExists)
    let witness := missing.map (destination / ·) |>.getD inventory
    buildUnlessUpToDate witness (← getTrace) (inventory.addExtension "trace") do
      proc {
        cmd := exe.toString
        args := #[mod.name.toString, destination.toString]
        env := ← getAugmentedEnv }
    addTrace (← computeTrace inventory)
    return destination

/-- Export each module's own datapack declarations, following the library's module selection. -/
library_facet datapack (lib) : Array FilePath := do
  let modules ← (← lib.modules.fetch).await
  pure <| Job.collectArray <| ← modules.mapM (fetch <| ·.facet `datapack)

/-- Export the datapacks in the package's Lean libraries. -/
package_facet datapack (pkg) : Array FilePath := do
  let jobs ← pkg.leanLibs.mapM (fetch <| ·.facet `datapack)
  return (Job.collectArray jobs).map (·.flatten)

lean_exe «oria-teleport» where root := `examples.Teleport
lean_exe «oria-dice» where root := `examples.Dice
lean_exe «oria-trigger» where root := `examples.Trigger
lean_exe «oria-rps» where root := `examples.RockPaperScissors
lean_exe «oria-ledger» where root := `examples.RoundLedger
lean_exe «oria-merge-sort» where root := `examples.MergeSort
lean_exe «datapack-artifact-test» where root := `tests.DatapackArtifact
lean_exe «persistent-artifact-test» where root := `tests.PersistentArtifact
lean_exe «value-types-artifact-test» where root := `tests.ValueTypesArtifact
lean_exe «failure-artifact-test» where root := `tests.FailureArtifact
lean_exe «optimization-artifact-test» where root := `tests.OptimizationArtifact
lean_exe «task-artifact-test» where root := `tests.TaskArtifact
lean_exe «register-artifact-test» where root := `tests.RegisterArtifact
lean_exe «calls-artifact-test» where root := `tests.CallsArtifact
lean_exe «nbt-artifact-test» where root := `tests.NbtArtifact
lean_exe «typed-nbt-artifact-test» where root := `tests.TypedNbtArtifact
lean_exe «global-nbt-artifact-test» where root := `tests.GlobalNbtArtifact
lean_exe «standard-command-artifact-test» where root := `tests.StandardCommandsArtifact
lean_exe «data-compute-artifact-test» where root := `tests.DataComputeArtifact
lean_exe «execute-artifact-test» where root := `tests.ExecuteArtifact
lean_exe «flow-artifact-test» where root := `tests.FlowArtifact
lean_exe «runtime-nbt-artifact-test» where root := `tests.RuntimeNbtArtifact
lean_exe «scoreboard-artifact-test» where root := `tests.ScoreboardArtifact
lean_exe «rps-artifact-test» where root := `tests.RockPaperScissorsArtifact
lean_exe «command-arguments-artifact-test» where root := `tests.CommandArgumentsArtifact
lean_exe «entity-command-artifact-test» where root := `tests.EntityCommandsArtifact
lean_exe «presentation-artifact-test» where root := `tests.PresentationArtifact
lean_exe «batch-artifact-test» where root := `tests.BatchArtifact
lean_exe «generation-artifact-test» where root := `tests.GenerationArtifact
lean_exe «utility-artifact-test» where root := `tests.UtilityArtifact
lean_exe «server-artifact-test» where root := `tests.ServerArtifact
