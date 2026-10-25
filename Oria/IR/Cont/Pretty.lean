module

public import Oria.Command.Pretty
public import Oria.IR.Cont.Definition
public import Oria.IR.Common.Format

namespace Oria.IR.Cont

open Std
open Std.Format

private abbrev Label (_ : ObjTy) := Nat

/-- Stable display levels for one intrinsically scoped lexical context. -/
private structure Names (Γ : List ObjTy) where
  labels : Args Label Γ
  next : Nat

namespace Names

private def initial (Γ : List ObjTy) : Names Γ :=
  { labels := Args.tabulate Γ fun i => i.val
    next := Γ.length }

private def extend {Γ : List ObjTy} (names : Names Γ) (a : ObjTy) : Names (a :: Γ) :=
  { labels := .cons names.next names.labels
    next := names.next + 1 }

private def telescope (types : List ObjTy) (first : Nat) : Args Label types :=
  Args.tabulate types fun i => first + i.val

private def extendMany {Γ : List ObjTy} (names : Names Γ) (types : List ObjTy) : Names (types ++ Γ) :=
  { labels := (telescope types names.next).append names.labels
    next := names.next + types.length }

private def lookup {Γ : List ObjTy} {a : ObjTy} (names : Names Γ) (x : Scope.Var Unit Γ a) : Nat :=
  names.labels.get x.index

end Names

private def formatLocal (label : Nat) : Format :=
  "%" ++ toString label

private def formatBinder (label : Nat) (type : ObjTy) : Format :=
  formatLocal label ++ " : " ++ type.format

private def formatLabels : {types : List ObjTy} → Args Label types → List Format
  | [], .nil => []
  | type :: _, .cons label rest =>
      formatBinder label type :: formatLabels rest

private def formatContext {Γ : List ObjTy} (names : Names Γ) : List Format :=
  formatLabels names.labels

private def application (name : Format) (arguments : List Format) : Format :=
  match arguments with
  | [] => name
  | _ => group <| name ++ nestD (line ++ joinSep arguments line)

private def commaLine : Format :=
  "," ++ line

private def tuple (items : List Format) : Format :=
  group <| "(" ++ nestD (joinSep items commaLine) ++ ")"

private def block (body : Format) : Format :=
  "{" ++ nest 2 (line ++ body) ++ line ++ "}"

private def formatAtom {Γ : List ObjTy} {a : ObjTy} (names : Names Γ) : Atom Γ a → Format
  | .local x => formatLocal (names.lookup x)
  | .unit => "()"
  | .bool true => "true"
  | .bool false => "false"
  | .i32 value => toString value

private def formatArgs {Γ : List ObjTy} {types : List ObjTy}
    (names : Names Γ) : Args (Atom Γ) types → List Format
  | .nil => []
  | .cons value rest => formatAtom names value :: formatArgs names rest

private def formatOp {Γ : List ObjTy} {g : Grade} {a : ObjTy} (names : Names Γ) : Op Γ g a → Format
  | .copy value => application "copy" [formatAtom names value]
  | .unary .neg value => application "neg" [formatAtom names value]
  | .unary .not value => application "not" [formatAtom names value]
  | .binary .add left right =>
      application "add" [formatAtom names left, formatAtom names right]
  | .binary .sub left right =>
      application "sub" [formatAtom names left, formatAtom names right]
  | .binary .mul left right =>
      application "mul" [formatAtom names left, formatAtom names right]
  | .division left right =>
      application "div" [formatAtom names left, formatAtom names right]
  | .binary .le left right =>
      application "le" [formatAtom names left, formatAtom names right]
  | .binary .lt left right => application "lt" [formatAtom names left, formatAtom names right]
  | .binary .eq left right => application "eq" [formatAtom names left, formatAtom names right]
  | .binary .beq left right => application "beq" [formatAtom names left, formatAtom names right]
  | .construct constructor arguments =>
      application ("construct " ++ constructor.name.toString) (formatArgs names arguments)
  | .call reference arguments =>
      let .named declaration := reference.key
      application ("call " ++ declaration.toString) (formatArgs names arguments)
  | .checkpoint forced => if forced then "yield" else "checkpoint"
  | .command request => request.formatWith (formatAtom names)
  | .execute scope ref args =>
      let .named name := ref.key
      scope.fragment.formatWith (formatAtom names) ++ " run " ++
        application ("call " ++ name.toString) (formatArgs names args)
  | .memory operation arguments => application operation.format (formatArgs names arguments)

mutual
  private def formatComp {Γ : List ObjTy} {joins : List (List ObjTy)} {result : ObjTy}
      (names : Names Γ)
      (labels : Args (fun _ : List ObjTy => Nat) joins) : Comp Γ result joins → Format
    | .fail => "fail"
    | .invoke (a := a) operation next failed =>
        "invoke " ++ formatOp names operation ++ " as " ++ formatBinder names.next a ++
          " " ++ block (formatComp (names.extend a) labels next) ++ " failure " ++
          block (formatComp names labels failed)
    | .ret value => "return " ++ formatAtom names value
    | .letOp (a := a) operation next =>
        "let " ++ formatBinder names.next a ++ " <- " ++ formatOp names operation ++ line ++
          formatComp (names.extend a) labels next
    | .branch condition yes no =>
        "if " ++ formatAtom names condition ++ " " ++ block (formatComp names labels yes) ++
          " else " ++ block (formatComp names labels no)
    | .switch scrutinee arms =>
        "switch " ++ formatAtom names scrutinee ++ " " ++
          block (formatArms names labels arms)
    | .letJoin (params := params) body next =>
        let label := joins.length
        let parameters := Names.initial params
        "join @" ++ toString label ++ tuple (formatContext parameters) ++ " " ++
          block (formatComp parameters labels body) ++ line ++
            formatComp names (.cons label labels) next
    | .jump target arguments =>
        "jump @" ++ toString (target.lookup labels) ++ tuple (formatArgs names arguments)

  private def formatArms {Γ : List ObjTy} {joins : List (List ObjTy)} {a : ObjTy} {result : ObjTy}
      (names : Names Γ)
      (labels : Args (fun _ : List ObjTy => Nat) joins) : Arms Γ a result joins → Format
    | .nil => nil
    | .default body => "_ => " ++ block (formatComp names labels body)
    | .cons (fields := fields) constructor body rest =>
        constructor.name.toString ++ tuple (formatLabels (Names.telescope fields names.next)) ++
          " => " ++ block (formatComp (names.extendMany fields) labels body) ++
          (match rest with
          | .nil => nil
          | _ => line ++ formatArms names labels rest)
end

public def Comp.format {Γ : List ObjTy} {a : ObjTy} {joins : List (List ObjTy)}
    (computation : Comp Γ a joins) : Format :=
  formatComp (Names.initial Γ) (Args.tabulate joins (fun i => joins.length - i.val - 1)) computation

public def Def.format {sig : Signature} (definition : Def sig) : Format :=
  let names := Names.initial sig.args
  let header := group <|
    "fn " ++ tuple (formatContext names) ++ " -> " ++
      sig.result.format ++ " " ++ sig.grade.format
  header ++ " " ++ block definition.computation.format

public instance {sig : Signature} : ToFormat (Def sig) where
  format := Def.format

public def Def.pretty {sig : Signature} (definition : Def sig) (width : Nat) : String :=
  definition.format.pretty width

end Oria.IR.Cont
