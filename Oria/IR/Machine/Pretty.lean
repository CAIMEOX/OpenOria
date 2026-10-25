module

public import Oria.IR.Machine.Program
public import Oria.Command.Pretty
public import Oria.IR.Common.Format

namespace Oria.IR.Machine

open Std Std.Format

private def tuple (values : List Format) : Format :=
  group ("(" ++ nest 2 (joinSep values ("," ++ line)) ++ ")")

private def braced (value : Format) : Format :=
  "{" ++ nest 2 (line ++ value) ++ line ++ "}"

private def localName (i : Nat) : Format := "%" ++ toString i

private def atom {n : Nat} (names : Vector Nat n) : Atom n → Format
  | .var i => localName (names.get i)
  | .lit value => toString value

private def values {n m : Nat} (names : Vector Nat n) (args : Vector (Atom n) m) : Format :=
  tuple (args.toList.map (atom names))

private def edge {n : Nat} {layout : List Nat} (names : Vector Nat n) (target : Edge layout n) : Format :=
  "b" ++ toString target.target.index.val ++ values names target.values

private def operation {n : Nat} {functions : List Signature} {m : Nat}
    (names : Vector Nat n) : Op functions n m → Format
  | .division left right => "div " ++ tuple [atom names left, atom names right]
  | .nbt op args => (MemoryOp.nbt op).format ++ " " ++
      tuple (args.foldl (fun out value => out ++ [atom names value]) [])
  | .checkpoint forced => if forced then "yield" else "checkpoint"
  | .unary .neg value => "neg " ++ atom names value
  | .unary .not value => "not " ++ atom names value
  | .binary operator left right =>
      let name : Format := match operator with
        | .add => "add" | .sub => "sub" | .mul => "mul" | .le => "le"
        | .lt => "lt" | .eq => "eq" | .beq => "beq"
      name ++ " " ++ tuple [atom names left, atom names right]
  | .call callee args => "call @" ++ toString callee.index.val ++ values names args
  | .command request => request.formatWith (fun value => atom names value)
  | .execute scope _ callee args =>
      scope.fragment.formatWith (fun value => atom names value) ++
        " run @" ++ toString callee.index.val ++ values names args
  | .allocate layout args =>
      "allocate " ++ layout.type.format ++ " tag=" ++ toString layout.tag ++
        " scan=" ++ toString layout.scanCode ++ " " ++ values names args
  | .tag value => "tag " ++ atom names value
  | .project layout value =>
      "project " ++ layout.constructor.toString ++ " " ++ atom names value
  | .promote type value => "promote " ++ type.format ++ " " ++ atom names value
  | .rootGet root => "root.get " ++ root.name.toString
  | .rootSet root args => "root.set " ++ root.name.toString ++ " " ++ values names args
  | .refNew layout args => "ref.new " ++ layout.type.format ++ " " ++ values names args
  | .refGet layout pointer => "ref.get " ++ layout.type.format ++ " " ++ atom names pointer
  | .refSet layout pointer args =>
      "ref.set " ++ layout.type.format ++ " " ++ atom names pointer ++ " " ++ values names args

private def condition {n : Nat} (names : Vector Nat n) : Condition (Atom n) → Format
  | .isTrue v => atom names v
  | .compare op l r =>
      let symbol : Format := match op with
        | .le => "<=" | .lt => "<" | .eq | .beq => "=="
      group (atom names l ++ " " ++ symbol ++ " " ++ atom names r)

private def terminator {n : Nat} {layout : List Nat} {result : Nat}
    (names : Vector Nat n) : Terminator layout result n → Format
  | .ret args => "return " ++ values names args
  | .jump target => "jump " ++ edge names target
  | .branch c yes no =>
      "branch " ++ condition names c ++ " " ++ edge names yes ++ " else " ++ edge names no
  | .switch value cases fallback =>
      let cases := cases.map fun (t, target) => toString t ++ " => " ++ edge names target
      let cases := cases ++ (fallback.toList.map fun target => "_ => " ++ edge names target)
      "switch " ++ atom names value ++ " " ++ braced (joinSep cases line)

private def body {n : Nat} {functions : List Signature} {layout : List Nat} {result : Nat}
    (names : Vector Nat n) : Body functions layout result n → Format
  | .done exit => terminator names exit
  | .step (m := m) op next =>
      let fresh := Vector.ofFn fun i : Fin m => n + i.val
      "let " ++ tuple (fresh.toList.map localName) ++ " = " ++ operation names op ++ line ++
        body (fresh ++ names) next

public def Def.format {functions : List Signature} {sig : Signature} (definition : Def functions sig) : Format :=
  let blocks := (List.finRange definition.layout.length).map fun i =>
    let count := definition.layout.get i
    let names := Vector.ofFn (fun i : Fin count => i.val)
    "b" ++ toString i.val ++ tuple (names.toList.map (fun i => localName i ++ " : word")) ++
      " " ++ braced (body names (definition.blocks.get i))
  "entry b" ++ toString definition.entry.index.val ++ " -> " ++ toString sig.result ++
    " words " ++ braced (joinSep blocks line)

public def Def.pretty {functions : List Signature} {sig : Signature}
    (definition : Def functions sig) (width : Nat) : String :=
  definition.format.pretty width

end Oria.IR.Machine
