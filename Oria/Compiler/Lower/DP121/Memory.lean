module

public import Oria.Compiler.Lower.DP121.Emit
public import Oria.Compiler.Lower.DP121.Arithmetic

namespace Oria.Lower.DP121.Memory

open Oria.Target.DP121

public inductive Space where
  | ephemeral
  | persistent
  | either

public def operand {k : Nat} (bank : Layout k) : Transfer.Source Place → List (Command .plain) × (Int32 ⊕ Score)
  | .imm value => ([], .inl value)
  | source =>
      let (commands, score) := Arithmetic.operand bank.scratch[0] source
      (commands, .inr score)

/-- Freeze the address before publishing any projected component. -/
public def project {k : Nat} (config : Config) (bank : Layout k) (path : String)
    (value : Transfer.Source Place) (fields : List (List Nbt.PathSegment × Place))
    (space : Space) : Except Diagnostic Emitted := do
  if fields.isEmpty then return ⟨[], []⟩
  let heap : Heap.Config := ⟨← config.runtime, config.objective⟩
  let (loaded, pointer) := operand bank value
  let ref : FunctionRef (.macro Heap.addressSchema) := .ofId (← config.function path).id
  match space with
  | .ephemeral =>
      pure ⟨loaded ++ Heap.address heap pointer ++ [.functionWithStorage ref (Heap.source heap)],
        [⟨.macro Heap.addressSchema, Heap.reader heap ref fields⟩]⟩
  | .persistent | .either =>
      let memory ← config.memory
      let index := Persistent.Runtime.score memory "#read_index"
      let selected := Persistent.Runtime.score memory "#read_space"
      let position : Fin Heap.addressSchema.fields.length := ⟨0, by simp [Heap.addressSchema]⟩
      let p0 : StoragePath :=
        ⟨memory.runtime, ⟨.key ⟨"memory_arg"⟩, [.key (Heap.addressSchema.parameterKey position)]⟩⟩
      let (prepare, source) ← match space with
        | .persistent => pure (Persistent.Runtime.address memory pointer, Persistent.Runtime.source memory)
        | .either =>
            let (copy, original) := match pointer with
              | .inl p => ([Command.scoreboard (.set index p)], index)
              | .inr p => ([], p)
            let commands := copy ++ [
              .scoreboard (.set selected 0),
              .when .positive (.matches original (.atLeast 1)) (.scoreboard (.set selected 1))]
            let commands := match pointer with
              | .inl p => commands ++ [.scoreboard (.set index (if p > 0 then p - 1 else -1 - p))]
              | .inr p => commands ++ [
                  .scoreboard (.set index (-1)),
                  .when .positive (.matches selected (.exact 0)) (.scoreboard (.operation index .subtract p)),
                  .when .positive (.matches selected (.exact 1)) (.scoreboard (.operation index .add p))]
            pure (commands ++ [.store .result (.storageI32 p0) (.scoreboard (.get index))],
              Persistent.Runtime.source memory)
        | .ephemeral => throw (.unsupportedMachineLowering .anonymous)
      let lines := fields.flatMap fun (suffix, target) =>
        let readAt (storage : ResourceId) (key : String) : Command (.macro Heap.addressSchema) :=
          let source : DataPath (.macro Heap.addressSchema) :=
            .index ⟨storage, .key key⟩ position suffix
          match target with
          | .score target => .store .result (.score target) (.data (.get source))
          | .storage target => .data (.setFrom target source)
        let p := readAt memory.storage "slots"
        match space with
        | .either => [
            FunctionLine.macro (.ofCommand
              (.when .positive (.matches selected (.exact 0)) (readAt memory.runtime "arena")) (by
                cases target <;>
                  simp [readAt, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount])),
            .macro (.ofCommand (.when .positive (.matches selected (.exact 1)) p) (by
              cases target <;>
                simp [p, readAt, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]))]
        | _ => [FunctionLine.macro (.ofCommand p (by
            cases target <;>
              simp [p, readAt, Command.parameterCount, DataCommand.parameterCount, DataPath.parameterCount]))]
      pure ⟨loaded ++ prepare ++ [.functionWithStorage ref source],
        [⟨.macro Heap.addressSchema, ⟨ref, .macro lines.toArray⟩⟩]⟩

end Oria.Lower.DP121.Memory
