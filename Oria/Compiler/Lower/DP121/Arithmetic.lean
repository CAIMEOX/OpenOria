module

public import Oria.Compiler.Lower.DP121.Stack
public import Oria.IR.Common.Operator
public import Oria.IR.Machine.Condition

namespace Oria.Lower.DP121.Arithmetic

open Oria.IR Oria.Target.DP121

private def copy (target : Place) (source : Transfer.Source Place) : List (Command .plain) :=
  if source == .loc target then [] else [Stack.move ⟨target, source⟩]

/-- Scalar memory operands use a fixed scratch; register sources stay in place. -/
public def operand (scratch : Score) : Transfer.Source Place → List (Command .plain) × Score
  | .loc (.score score) => ([], score)
  | source => (copy (.score scratch) source, scratch)

private def arithmetic {k : Nat} (bank : Layout k) (op : Oria.Command.ScoreOp) (target : Place)
    (left right : Transfer.Source Place) : List (Command .plain) :=
  let out := match target with | .score score => score | .storage _ => bank.scratch[2]
  let (left, right) :=
    if (op == .add || op == .multiply) && right == .loc (.score out) then (right, left)
    else (left, right)
  let (beforeRight, rhs) :=
    if right == .loc (.score out) && left != .loc (.score out) then
      (copy (.score bank.scratch[0]) right, bank.scratch[0])
    else operand bank.scratch[0] right
  beforeRight ++ copy (.score out) left ++ [.scoreboard (.operation out op rhs)] ++
    copy target (.loc (.score out))

private def immediate {k : Nat} (bank : Layout k) (subtract : Bool) (target : Place)
    (left : Transfer.Source Place) (right : Int32) : List (Command .plain) :=
  let out := match target with | .score score => score | .storage _ => bank.scratch[2]
  let emit (command : Scoreboard) := copy (.score out) left ++
    [.scoreboard command] ++ copy target (.loc (.score out))
  if h : 0 ≤ right then
    emit (if subtract then .remove out right h else .add out right h)
  else if h : 0 ≤ -right then
    emit (if subtract then .add out (-right) h else .remove out (-right) h)
  else arithmetic bank (if subtract then .subtract else .add) target left (.imm right)

/-- Capture native scoreboard failure and quotient separately, reading both operands
before publishing either result into possibly aliased homes. -/
public def division {k : Nat} (bank : Layout k) (targets : Vector (Option Place) 2)
    (left right : Transfer.Source Place) : List (Command .plain) :=
  let out := match targets[1] with
    | some (.score s) => if targets[0] == targets[1] then bank.scratch[2] else s
    | _ => bank.scratch[2]
  let success := match targets[0] with
    | some (.score s) => s
    | _ => bank.scratch[1]
  let (prepare, rhs) :=
    if right == .loc (.score out) && left != .loc (.score out) then
      (copy (.score bank.scratch[0]) right, bank.scratch[0])
    else operand bank.scratch[0] right
  let command := Command.scoreboard (mode := .plain) (.operation out .divide rhs)
  prepare ++ copy (.score out) left ++
    [if targets[0].isSome then .store .success (.score success) command else command] ++
    (targets[0].toList.flatMap fun target => copy target (.loc (.score success))) ++
    (targets[1].toList.flatMap fun target => copy target (.loc (.score out)))

public def unary {k : Nat} {a b : ObjTy}
    (bank : Layout k) : UnaryOp a b → Place → Transfer.Source Place → List (Command .plain)
  | .neg, target, value =>
  let out := match target with | .score s => s | .storage _ => bank.scratch[2]
  let (before, source) := if value == .loc (.score out) then
    (copy (.score bank.scratch[0]) value, bank.scratch[0])
    else operand bank.scratch[0] value
  before ++ [.scoreboard (.set out 0), .scoreboard (.operation out .subtract source)] ++
    copy target (.loc (.score out))
  | .not, target, value =>
    let (before, source) := operand bank.scratch[0] value
    let out := bank.scratch[2]
    before ++ [.scoreboard (.set out 0),
      .when .positive (.matches source (.exact 0)) (.scoreboard (.set out 1))] ++
      copy target (.loc (.score out))

private def comparison {k : Nat} (bank : Layout k) (relation : ScoreRelation)
    (left right : Transfer.Source Place) : List (Command .plain) × ScoreCondition :=
  let ranged (source : Transfer.Source Place) (range : IntRange) :=
    let (before, score) := operand bank.scratch[0] source
    (before, ScoreCondition.matches score range)
  match relation, left, right with
  | .equal, l, .imm r => ranged l (.exact r)
  | .equal, .imm l, r => ranged r (.exact l)
  | .lessOrEqual, l, .imm r => ranged l (.atMost r)
  | .lessOrEqual, .imm l, r => ranged r (.atLeast l)
  | .less, l, .imm r =>
      if r > -2147483648 then ranged l (.atMost (r - 1)) else general
  | .less, .imm l, r =>
      if l < 2147483647 then ranged r (.atLeast (l + 1)) else general
  | _, _, _ => general
where
  general :=
    let (beforeLeft, lhs) := operand bank.scratch[0] left
    let (beforeRight, rhs) := operand bank.scratch[1] right
    (beforeLeft ++ beforeRight, ScoreCondition.compare lhs relation rhs)

/-- Select a predicate after allocation, reading operands before either outgoing edge runs. -/
public def condition {k : Nat} (bank : Layout k) :
    Machine.Condition (Transfer.Source Place) → List (Command .plain) × ScoreCondition
  | .isTrue value =>
      let (before, score) := operand bank.scratch[0] value
      (before, .matches score (.exact 1))
  | .compare op l r => comparison bank
      (match op with | .le => .lessOrEqual | .lt => .less | .eq | .beq => .equal) l r

private def compare {k : Nat} (bank : Layout k) (relation : ScoreRelation) (target : Place)
    (left right : Transfer.Source Place) : List (Command .plain) :=
  let (before, test) := comparison bank relation left right
  let out := bank.scratch[2]
  before ++ [.scoreboard (.set out 0),
    .when .positive test (.scoreboard (.set out 1))] ++
    copy target (.loc (.score out))

/-- Inputs are read before a possibly aliased output is published. -/
public def binary {k : Nat} {a b c : ObjTy}
    (bank : Layout k) (op : BinaryOp a b c) (target : Place)
    (left right : Transfer.Source Place) : List (Command .plain) :=
  match op with
  | .add => match left, right with
      | l, .imm r | .imm r, l => immediate bank false target l r
      | _, _ => arithmetic bank .add target left right
  | .sub => match right with
      | .imm r => immediate bank true target left r
      | _ => arithmetic bank .subtract target left right
  | .mul => arithmetic bank .multiply target left right
  | .le => compare bank .lessOrEqual target left right
  | .lt => compare bank .less target left right
  | .eq | .beq => compare bank .equal target left right

end Oria.Lower.DP121.Arithmetic
