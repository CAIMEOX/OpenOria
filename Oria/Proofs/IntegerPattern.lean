module

import Oria
import Oria.Compiler.Definition
import Oria.IR.Cont.Semantics
import Oria.Proofs.McFunctionUtil
meta import Oria
meta import Oria.Compiler.Definition
meta import Oria.IR.Cont.Semantics
meta import Oria.Proofs.McFunctionUtil

namespace Oria.Proofs.IntegerPattern

open Oria.IR Lean Lean.Elab.Command
open Oria.Semantics.Cont
open Oria.Proofs.McFunctionUtil

@[mcfunction]
private def classify (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | 0 => return 10
  | _ => return 20

private def compile (d : ElaboratedDef) : Except Diagnostic (IR.Cont.Def d.signature) := do
  Compiler.compile (← Function.Catalog.build []) (← ObjectCatalog.build [])
    (← Oria.Command.Catalog.build []) d

private def lower (types : List ObjTy) (name : Name) : CommandElabM (IR.Cont.Def ⟨types, .i32, .pure⟩) := do
  let d ← elaborate name
  let .ok result := compile d | throwError "integer pattern compilation failed: {name}"
  if h : d.signature = ⟨types, .i32, .pure⟩ then
    pure (h ▸ result)
  else throwError "unexpected signature for {name}"

private def model : Model Unit := {
  unary := fun _ _ => pure .failed
  binary := fun
    | .eq, .i32 x, .i32 y => pure (.returned (.bool (x == y)))
    | _, _, _ => pure .failed
  construct := fun _ _ => pure .failed
  call := fun _ _ => pure .failed
  command := fun _ => pure .failed
  execute := fun _ _ _ => pure .failed
  memory := fun _ _ => pure .failed
  project := fun _ _ => pure none }

private def check {types : List ObjTy} (name : Name) (cases : List (Env types × Int32)) : CommandElabM Unit := do
  let d ← lower types name
  for (env, expected) in cases do
    match (eval model 200 env .nil d.computation).run' () with
    | some (.returned (.i32 actual)) =>
      unless actual == expected do throwError "{name}: expected {expected}, got {actual}"
    | _ => throwError "{name}: evaluation failed"

run_cmd
  check ``classify [(.cons (.i32 0) .nil, 10), (.cons (.i32 42) .nil, 20)]

@[mcfunction]
private def signed (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | -2147483648 => return 1
  | -1 => return 2
  | 0 => return 3
  | 2147483647 => return 4
  | n => return n

run_cmd
  check ``signed <| [(Int32.minValue, 1), (-1, 2), (0, 3), (Int32.maxValue, 4), (37, 37)].map
    fun (n, result) => (.cons (.i32 n) .nil, result)

@[mcfunction]
private def priority (x y : Val Int32) : Prog .pure Int32 := do
  match x, y with
  | _, 0 => return 1
  | 0, _ => return 2
  | 1, -1 => return 3
  | _, y => return y

run_cmd
  check ``priority <| [(0, 0, 1), (0, 2, 2), (1, -1, 3), (1, 7, 7), (-1, 0, 1)].map
    fun (x, y, result) => (.cons (.i32 x) (.cons (.i32 y) .nil), result)

@[mcfunction]
private def nested (x : Val (Option Int32)) (y : Val Int32) : Prog .pure Int32 := do
  match x, y with
  | .some 0, _ => return 10
  | .some n, 0 => return n
  | .some (-1), _ => return 20
  | .none, 7 => return 30
  | _, y => return y

run_cmd
  check ``nested <| [(some 0, 9, 10), (some (-1), 0, -1), (some (-1), 9, 20),
      (some 4, 5, 5), (none, 7, 30), (none, 8, 8)].map fun (x, y, result) =>
    (.cons (match x with | some n => .some (.i32 n) | none => .none)
      (.cons (.i32 y) .nil), result)

@[mcfunction]
private def incomplete (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | 0 => return 0

@[mcfunction]
private def duplicate (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | 0 => return 1
  | 0 => return 2
  | _ => return 3

@[mcfunction]
private def shadowed (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | _ => return 1
  | 0 => return 2

@[mcfunction]
private def wrapped (n : Val Int32) : Prog .pure Int32 := do
  match n with
  | -1 => return 1
  | 4294967295 => return 2
  | _ => return 3

@[mcfunction]
private def incompleteNested (x : Val (Option Int32)) (n : Val Int32) : Prog .pure Int32 := do
  match x, n with
  | .some _, _ => return 0
  | .none, 0 => return 1

@[mcfunction]
private def covered (x y : Val Int32) : Prog .pure Int32 := do
  match x, y with
  | _, 0 => return 1
  | 0, 0 => return 2
  | _, _ => return 3

run_cmd
  for name in [``incomplete, ``incompleteNested] do
    let d ← elaborate name
    match compile d with
    | .error (.nonExhaustiveMatch _) => pure ()
    | _ => throwError "expected integer exhaustiveness diagnostic in {name}"
  for name in [``duplicate, ``shadowed, ``wrapped, ``covered] do
    let d ← elaborate name
    match compile d with
    | .error (.redundantPattern _ 1) => pure ()
    | _ => throwError "expected redundant second row in {name}"

end Oria.Proofs.IntegerPattern
