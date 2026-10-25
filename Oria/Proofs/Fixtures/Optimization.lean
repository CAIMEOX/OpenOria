module

public import Oria
public import Oria.Datapack
meta import Oria
meta import Oria.Datapack

namespace Oria.Proofs.Fixtures.Optimization

open Oria.Std Oria.Std.Command.Arg Oria.Datapack

private def points : Command.Objective := "opt.results"

public structure Pair where
  x : Int32
  y : Int32
  deriving Oria.Object

@[mcfunction]
private def sum (p : Val Pair) : Prog .pure Int32 := return p.x + p.y

@[mcfunction]
private def identity (x : Val Int32) : Prog .pure Int32 := return (x + 0) * 1

@[mcfunction]
private def succeeded := show Prog _ Int32 from do
  let ok ← (Scoreboard.get (.named "#input") points).isSuccess
  if ok then return 1 else return 0

@[mcfunction]
private def absent := show Prog _ Int32 from do
  let ok ← (Scoreboard.get (.named "#missing") points).isSuccess
  if ok then return 1 else return 0

@[mcfunction]
private def setup := (Scoreboard.Objectives.add points .dummy).ignore

@[mcfunction]
private def left (n : Val Int32) := Scoreboard.add (.one (.named "#count")) points n

@[mcfunction]
private def right (n : Val Int32) := Scoreboard.add (.one (.named "#count")) points n

@[mcfunction]
private def arithmetic (x : Val Int32) : Prog .pure Int32 := do
  let unused ← Prog.pure (x * x)
  return x + 1

@[mcfunction]
private def divide (x y : Val Int32) : Prog .failure Int32 := x / y

@[mcfunction]
private def neutral (x : Val Int32) : Prog .failure Int32 := do
  let y ← x / 1
  return y + (x - x)

@[mcfunction]
private def neutralEntry := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") points
  let y ← neutral.call n
  Scoreboard.set (.named "#neutral") points y

@[datapack]
public def identities : Spec := build {ns := "identity_test"} do
  entry "run" neutralEntry.ref

@[mcfunction]
private def joined (n : Val Int32) := show Prog _ Int32 from do
  let mode ← (show Prog _ Int32 from do
    if n < 0 then
      Scoreboard.set (.named "#join_path") points 1
      return 3
    else
      Scoreboard.set (.named "#join_path") points 2
      return 3)
  let input ← Scoreboard.get (.named "#input") points
  if mode == 0 then
    Scoreboard.set (.named "#dead_join") points 1
  return mode + input

@[mcfunction]
private def predicate (n : Val Int32) : Prog .pure Int32 := do
  if n != 0 then return 11 else return 13

@[mcfunction]
private def predicateEntry := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") points
  let p ← predicate.call n
  Scoreboard.set (.named "#predicate") points p

@[datapack]
public def predicates : Spec := build {ns := "pred_test"} do
  entry "run" predicateEntry.ref

@[mcfunction]
private def across (n : Val Int32) := show Prog _ Int32 from do
  let ready := n != 0
  let y ← Scoreboard.get (.named "#input") points
  if ready then return n + y else return n - y

@[mcfunction]
private def acrossEntry := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") points
  let y ← across.call n
  Scoreboard.set (.named "#across") points y

@[mcfunction]
private def threaded (n : Val Int32) := show Prog _ Int32 from do
  let chosen ← (show Prog _ Bool from do
    if n < 0 then
      Scoreboard.set (.named "#thread_path") points 1
      return Bool.lit true
    else
      Scoreboard.set (.named "#thread_path") points 2
      return Bool.lit false)
  if !chosen then return n + 1 else return n - 1

@[mcfunction]
private def threadedEntry := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") points
  let y ← threaded.call n
  Scoreboard.set (.named "#threaded") points y

@[datapack]
public def crossPredicates : Spec := build {ns := "cross_pred"} do
  entry "run" acrossEntry.ref
  entry "threaded" threadedEntry.ref

@[mcfunction]
private def selectedPredicate (n : Val Int32) := show Prog _ Int32 from do
  let ready ← (show Prog .pure Bool from do
    if n < 0 then return n < -5 else return n > 5)
  Scoreboard.set (.named "#observed") points n
  if ready then return n + 1 else return n - 1

@[mcfunction]
private def carriedPredicate (n : Val Int32) : Prog .pure Int32 := do
  let rec go (i : Val Int32) (ready : Val Bool) : Prog .pure Int32 := do
    if i <= 0 then
      if ready then return n else return -n
    go (i - 1) (!ready)
  go 3 (n != 0)

@[mcfunction]
private def varied (n : Val Int32) : Prog .pure Int32 := do
  let mode ← (show Prog .pure Int32 from do
    if n < 0 then return 3 else return 4)
  return mode + n

@[mcfunction]
private def loop (n : Val Int32) : Prog .pure Int32 := do
  let rec go (i total : Val Int32) : Prog .pure Int32 := do
    if i <= 0 then return total
    go (i - 1) (total + i)
  go n 0

private structure Fields where
  a : Int32
  b : Int32
  c : Int32
  deriving Nbt.Repr

private def fields : Nbt.Global (Array Fields) :=
  Nbt.Global.init "fields" (.key "values") #[⟨1, 2, 3⟩, ⟨10, 20, 30⟩]

@[mcfunction]
private def repeated (i : Val Int32) := show Prog _ Int32 from do
  let a ← fields[i].a
  let b ← fields[i].b
  let c ← fields[i].c
  return a + b + c

@[mcfunction]
private def repeatedEntry := show Prog _ Unit from do
  let n ← repeated.call 1
  Scoreboard.set (.named "#repeated") points n

@[datapack]
public def macros : Spec := build {ns := "reuse_test"} do
  global fields
  entry "run" repeatedEntry.ref

@[mcfunction]
private def noisy (i : Val Int32) := show Prog _ Int32 from do
  let n ← fields[i].c
  return n

@[mcfunction]
private def invalidation (i : Val Int32) := show Prog _ Int32 from do
  let a ← fields[i].a
  let other ← noisy.call (1 - i)
  let b ← fields[i].b
  let c ← fields[1 - i].c
  let d ← fields[i].c
  let same ← (Nbt.set fields ((Nbt.Access.root.at i).then Fields.Nbt.a) (.i32 a)).isSuccess
  if same then Prog.fail
  let missing ← (Nbt.readI32 fields ((Nbt.Access.root.at (99 : Val Int32)).then Fields.Nbt.a)).isSuccess
  if missing then Prog.fail
  fields[i].a := a + 1
  let changed ← fields[i].a
  if changed != a + 1 then Prog.fail
  fields[i].a := a
  return a + other + b + c + d + i

@[mcfunction]
private def captureAlias (i : Val Int32) := show Prog _ Int32 from do
  let found ← (Nbt.readI32 fields ((Nbt.Access.root.at i).then Fields.Nbt.a)).isSuccess
  let next ← (show Prog .pure Int32 from do
    if found then return 1 else return 0)
  let value ← fields[next].b
  return value

@[mcfunction]
private def stopping := show Prog _ Unit from do
  Scoreboard.get (.named "#missing") points
  Scoreboard.set (.named "#skipped") points 1

@[mcfunction]
private def run := show Prog _ Unit from do
  let n ← Scoreboard.get (.named "#input") points
  neutralEntry.call
  acrossEntry.call
  threadedEntry.call
  let negative ← threaded.call (-7)
  Scoreboard.set (.named "#threaded_negative") points negative
  let no ← across.call 0
  Scoreboard.set (.named "#across_zero") points no
  let yes ← selectedPredicate.call (-7)
  Scoreboard.set (.named "#selected_yes") points yes
  let no ← selectedPredicate.call n
  Scoreboard.set (.named "#selected_no") points no
  let carried ← carriedPredicate.call n
  Scoreboard.set (.named "#carried") points carried
  let min ← neutral.call (-2147483648)
  Scoreboard.set (.named "#neutral_min") points min
  (left.call n).ignore
  (right.call n).ignore
  Execute.forEach [] do
    left.call n
  let y ← arithmetic.call n
  Scoreboard.set (.named "#next") points y
  let joined ← joined.call n
  Scoreboard.set (.named "#joined") points joined
  predicateEntry.call
  let zero ← predicate.call 0
  Scoreboard.set (.named "#predicate_zero") points zero
  let v ← varied.call n
  Scoreboard.set (.named "#varied") points v
  let v ← varied.call (-7)
  Scoreboard.set (.named "#varied_negative") points v
  let total ← loop.call n
  Scoreboard.set (.named "#loop") points total
  let q ← n / 2
  Scoreboard.set (.named "#constant_divisor") points q
  let safe ← (n / 2).isSuccess
  if !safe then Scoreboard.set (.named "#dead_divisor") points 1
  let zero ← (n / 0).isSuccess
  if zero then Scoreboard.set (.named "#dead_zero") points 1
  (n / 0).ignore
  repeatedEntry.call
  let cached ← invalidation.call 0
  Scoreboard.set (.named "#invalidation0") points cached
  let cached ← invalidation.call 1
  Scoreboard.set (.named "#invalidation1") points cached
  let alias ← captureAlias.call 99
  Scoreboard.set (.named "#alias_missing") points alias
  let alias ← captureAlias.call 1
  Scoreboard.set (.named "#alias_present") points alias
  let p ← Pair.mk n (n + 1)
  let total ← sum.call p
  Scoreboard.set (.named "#projection") points total
  let v ← identity.call n
  Scoreboard.set (.named "#identity") points v
  let bit ← succeeded.call
  Scoreboard.set (.named "#bit") points bit
  let bit ← absent.call
  Scoreboard.set (.named "#missing_bit") points bit
  Scoreboard.set (.named "#minimum_add") points (n + (-2147483648 : Val Int32))
  Scoreboard.set (.named "#minimum_sub") points (n - (-2147483648 : Val Int32))
  Scoreboard.set (.named "#minus_one") points (n + (-1 : Val Int32))
  Execute.forEach [] do
    Scoreboard.set (.named "#fork") points 1
  Scoreboard.set (.named "#negative") points (-999 : Val Int32)
  let quotient ← (-7 : Val Int32) / 2
  Scoreboard.set (.named "#division") points quotient
  let quotient ← divide.call (-7) 2
  Scoreboard.set (.named "#runtime_division") points quotient
  let zero ← ((7 : Val Int32) / 0).isSuccess
  if zero then Prog.fail
  let zero ← (divide.call 7 0).isSuccess
  if zero then Prog.fail
  Scoreboard.set (.named "#zero_failure") points 1
  let quotient ← divide.call (-2147483648) (-1)
  Scoreboard.set (.named "#division_overflow") points quotient
  Scoreboard.set (.named "#overflow") points ((2147483647 : Val Int32) + 1)
  if (2 + 3 : Val Int32) == 5 then
    Scoreboard.set (.named "#chosen") points 1
  else
    Scoreboard.set (.named "#dead_branch") points 1
  stopping.call.ignore
  Scoreboard.set (.named "#after") points 1

@[mcfunction]
private def emptyA : Prog .pure Unit := return Val.unit

@[mcfunction]
private def emptyB : Prog .pure Unit := return Val.unit

private def entries : Builder Unit := do
  global fields
  onLoad setup.ref
  entry "run" run.ref
  entry "empty-a" emptyA.ref
  entry "empty-b" emptyB.ref

@[datapack]
public def specimen : Spec := build {ns := "opt_test", registerBudget := 128} entries

@[datapack]
public def allStack : Spec := build {ns := "opt_zero", registerBudget := 6} entries

end Oria.Proofs.Fixtures.Optimization
