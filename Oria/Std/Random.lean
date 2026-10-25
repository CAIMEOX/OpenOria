module

public import Oria.Std.Command.Arg
import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Random numbers and named sequences

`value` samples an integer, `roll` also broadcasts it, and `reset` manages random sequence state.
`Range` includes both endpoints, each of which may be static or computed at runtime.
Sampling changes random state. Executing the same generated action twice performs two draws.

Omitting the sequence name uses the current dimension's random source. Named sequences live
at server scope and provide independent random streams. See the
[standard library guide](##Oria.Std) for command results and `discard`.
-/

namespace Oria.Std.Random

open Oria.Std.Command.Arg

/-- Sampling effects. The default random source requires a dimension; named sequences require no context. -/
@[expose] public def grade (sequence : Option ResourceId := none) : Grade :=
  ⟨match sequence with
    | none => Req.dimension
    | some _ => Req.none, Eff.random ||| Eff.failure⟩

/-- Sampling and broadcasting effects, adding chat effects to the sampling requirements. -/
@[expose] public def rollGrade (sequence : Option ResourceId := none) : Grade :=
  ⟨match sequence with
    | none => Req.dimension
    | some _ => Req.none, Eff.random ||| Eff.chat ||| Eff.failure⟩

/-- Reset effects. Resetting one sequence requires a dimension; resetting all uses server state. -/
@[expose] public def resetGrade (sequences : Sequences) : Grade :=
  ⟨(Oria.Command.encode sequences).fragment.requirements, Eff.random ||| Eff.failure⟩

private def valueImpl (range : Range) :=
  Oria.Command.emit <| Command.Declarations.randomValue.call <|
    .cons (Oria.Command.encode range) .nil

private def valueSequenceImpl (range : Range) (id : ResourceId) :=
  Oria.Command.emit <| Command.Declarations.randomValueSequence.call <|
    .cons (Oria.Command.encode range) <| .cons (Oria.Command.encode id) .nil

/--
Sample an I32 from an inclusive range and return it on success. An optional name selects
an independent random sequence. Minecraft requires between 2 and 2147483647 candidate values;
singleton, reversed, and oversized ranges fail.

```lean
open Oria Oria.Std
example := Random.value (.between (.static 1) (.static 6))
example (lo hi : Val Int32) :=
  Random.value (.between (.dynamic lo) (.dynamic hi)) (some "demo:dice")
```
-/
public def value (range : Range) (sequence : Option ResourceId := none) :
    Prog (grade sequence) Int32 :=
  match sequence with
  | none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Range.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
        Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
        Command.Declarations.randomValue, Range.encode_requirements,
        Range.encode_fragment_requirements, ResourceId.encode_requirements,
        ResourceId.encode_fragment_requirements, Oria.Command.Fragment.token,
        Oria.Command.Fragment.require, Req.none, BitVec.or_assoc] using
        valueImpl range
  | some id => by
      simpa [Eff.failure, Grade.seq, Grade.failure, grade, Range.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
        Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
        Command.Declarations.randomValueSequence, Range.encode_requirements,
        Range.encode_fragment_requirements, ResourceId.encode_requirements,
        ResourceId.encode_fragment_requirements, Oria.Command.Fragment.token,
        Oria.Command.Fragment.require, Req.none, BitVec.or_assoc] using
        valueSequenceImpl range id

private def rollImpl (range : Range) :=
  Oria.Command.emit <| Command.Declarations.randomRoll.call <|
    .cons (Oria.Command.encode range) .nil

private def rollSequenceImpl (range : Range) (id : ResourceId) :=
  Oria.Command.emit <| Command.Declarations.randomRollSequence.call <|
    .cons (Oria.Command.encode range) <| .cons (Oria.Command.encode id) .nil

/-- Sample and broadcast Minecraft's roll message. Returns the sampled I32 on success.
Range restrictions and failure conditions follow {name}`Oria.Std.Random.value`, with
additional chat effects. -/
public def roll (range : Range) (sequence : Option ResourceId := none) :
    Prog (rollGrade sequence) Int32 :=
  match sequence with
  | none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, rollGrade, Range.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
        Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
        Command.Declarations.randomRoll, Range.encode_requirements,
        Range.encode_fragment_requirements, ResourceId.encode_requirements,
        ResourceId.encode_fragment_requirements, Oria.Command.Fragment.token,
        Oria.Command.Fragment.require, Req.none, BitVec.or_assoc] using
        rollImpl range
  | some id => by
      simpa [Eff.failure, Grade.seq, Grade.failure, rollGrade, Range.requirements, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
        Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
        Command.Declarations.randomRollSequence, Range.encode_requirements,
        Range.encode_fragment_requirements, ResourceId.encode_requirements,
        ResourceId.encode_fragment_requirements, Oria.Command.Fragment.token,
        Oria.Command.Fragment.require, Req.none, BitVec.or_assoc] using
        rollSequenceImpl range id

private def resetImpl (sequences : Sequences) :=
  Oria.Command.emit <| Command.Declarations.randomReset.call <|
    .cons (Oria.Command.encode sequences) .nil

private def resetSeedImpl (sequences : Sequences) (seed : Seed) :=
  Oria.Command.emit <| Command.Declarations.randomResetSeed.call <|
    .cons (Oria.Command.encode sequences) <| .cons (Oria.Command.encode seed) .nil

/--
Reset the selected random state. The success payload is the reset count reported by the
native command. Omitting the seed retains the server's default settings. Supplying
{name}`Oria.Std.Command.Arg.Seed` specifies the seed and both mixing flags explicitly.
Resetting all sequences with a seed also updates the defaults.

```lean
open Oria Oria.Std
example := Random.reset (.one "demo:dice")
  (some {value := .static 42, includeWorldSeed := false, includeSequenceId := false})
```
-/
public def reset (sequences : Sequences) (seed : Option Seed := none) :
    Prog (resetGrade sequences) Int32 :=
  match seed with
  | none => by
      simpa [Eff.failure, Grade.seq, Grade.failure, resetGrade, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
        Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
        Command.Declarations.randomReset, Oria.Command.Fragment.token,
        Oria.Command.Fragment.require, Req.none] using
        resetImpl sequences
  | some seed => by
      simpa [Eff.failure, Grade.seq, Grade.failure, resetGrade, Oria.Command.Call.grade,
        Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
        Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
        Command.Declarations.randomResetSeed, Seed.encode_requirements,
        Seed.encode_fragment_requirements,
        Oria.Command.Fragment.token,
        Oria.Command.Fragment.require, Oria.Command.Fragment.spaced,
        Oria.Command.Fragment.append, Oria.Command.Fragment.prepend,
        Req.none, BitVec.or_assoc] using
        resetSeedImpl sequences seed

end Oria.Std.Random
