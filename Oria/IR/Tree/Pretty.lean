module

public import Oria.Command.Pretty
public import Oria.IR.Common.Format
public import Oria.IR.Tree.Definition
import all Oria.IR.Common.Local
import all Oria.IR.Tree.Definition

namespace Oria.IR.Tree

open Std
open Std.Format

private def formatLocal {α : Type} {a : α} (name : Local a) : Format :=
  s!"%{name.serial}"

private def parenthesize (needed : Bool) (document : Format) : Format :=
  if needed then "(" ++ group document ++ ")" else document

private def formatInfix
    (context precedence : Nat)
    (operator left right : Format) : Format :=
  let document := left ++ line ++ operator ++ " " ++ right
  parenthesize (precedence < context) document

private def formatExpr {a : ObjTy} : (context : Nat) → Expr a → Format
  | _, .local name => formatLocal name
  | _, .unit => "()"
  | _, .bool true => "true"
  | _, .bool false => "false"
  | _, .i32 value => toString value
  | context, .unary .neg (.i32 value) =>
      let operand :=
        if value < 0 then "(" ++ toString value ++ ")" else toString value
      parenthesize (80 < context) ("-" ++ operand)
  | context, .unary .neg value =>
      parenthesize (80 < context) ("-" ++ formatExpr 81 value)
  | context, .unary .not value =>
      parenthesize (80 < context) ("!" ++ formatExpr 81 value)
  | context, .binary .add left right =>
      formatInfix context 60 "+" (formatExpr 60 left) (formatExpr 61 right)
  | context, .binary .sub left right =>
      formatInfix context 60 "-" (formatExpr 60 left) (formatExpr 61 right)
  | context, .binary .mul left right =>
      formatInfix context 70 "*" (formatExpr 70 left) (formatExpr 71 right)
  | context, .binary .le left right =>
      formatInfix context 50 "<=" (formatExpr 50 left) (formatExpr 51 right)
  | context, .binary .lt left right =>
      formatInfix context 50 "<" (formatExpr 50 left) (formatExpr 51 right)
  | context, .binary .eq left right | context, .binary .beq left right =>
      formatInfix context 50 "==" (formatExpr 50 left) (formatExpr 51 right)
  | context, .ite condition yes no =>
      parenthesize (0 < context) <| group (
        "if " ++ formatExpr 0 condition ++ line ++ "then " ++ formatExpr 0 yes ++
          line ++ "else " ++ formatExpr 0 no)
  | _, .project constructor field value =>
      group (formatExpr 100 value ++ "." ++ toString field.index.val ++
        "[" ++ constructor.name.toString ++ "]")

public def Expr.format {a : ObjTy} (expression : Expr a) : Format :=
  group (formatExpr 0 expression)

private def application (name : Format) (arguments : List Format) : Format :=
  match arguments with
  | [] => name
  | _ => group <| name ++ nestD (line ++ joinSep arguments line)

private def commaLine : Format :=
  "," ++ line

private def exprArgs {types : List ObjTy} : Args Expr types → List Format
  | .nil => []
  | .cons expression rest => formatExpr 100 expression :: exprArgs rest

private def formatLocals : {types : List ObjTy} → Args Local types → List Format
  | [], .nil => []
  | ty :: _, .cons name rest =>
      (formatLocal name ++ " : " ++ ty.format) :: formatLocals rest

private def block (body : Format) : Format :=
  "{" ++ nest 2 (line ++ body) ++ line ++ "}"

public def Prim.format {g : Grade} {a : ObjTy} : Prim g a → Format
  | .division left right => formatInfix 0 70 "/" (formatExpr 70 left) (formatExpr 71 right)
  | .checkpoint forced => if forced then "yield" else "checkpoint"
  | .construct constructor arguments =>
      application ("construct " ++ constructor.name.toString) (exprArgs arguments)
  | .call reference arguments =>
      let .named declaration := reference.key
      application ("call " ++ declaration.toString) (exprArgs arguments)
  | .recur reference arguments => application ("recur " ++ formatLocal reference) (exprArgs arguments)
  | .command request => request.formatWith Expr.format
  | .execute scope reference arguments =>
      let .named name := reference.key
      scope.fragment.formatWith Expr.format ++ " run " ++ application name.toString (exprArgs arguments)
  | .memory operation arguments => application operation.format (exprArgs arguments)

private def formatConstructor {a : ObjTy} {fields : List ObjTy} : Constructor a fields → Format
  | .data constructor => constructor.name.toString
  | .none => "option.none"
  | .some => "option.some"

mutual
  private def formatPattern {a : ObjTy} {bindings : List ObjTy} (pattern : Pattern a bindings)
      (locals : Args Local bindings) : Format :=
    match pattern, locals with
    | .any, .nil => "_"
    | .i32 value, .nil => toString value
    | .bind, .cons name .nil => formatLocal name ++ " : " ++ a.format
    | .ctor constructor fields, locals =>
        formatConstructor constructor ++ "(" ++
          joinSep (formatPatterns fields locals) commaLine ++ ")"

  private def formatPatterns {types : List ObjTy} {bindings : List ObjTy}
      (patterns : Patterns types bindings)
      (locals : Args Local bindings) : List Format :=
    match patterns with
    | .nil => []
    | .cons head rest =>
        let (headLocals, restLocals) := locals.split
        formatPattern head headLocals :: formatPatterns rest restLocals
end

mutual
  private def formatTreeRep {g : Grade} {a : ObjTy} : TreeRep g a → Format
    | .fail => "fail"
    | .catching body handler => "try " ++ block (formatTreeRep body) ++ " catch " ++ block (formatTreeRep handler)
    | .ret value => "return " ++ value.format
    | .perform primitive => "perform " ++ primitive.format
    | .weaken (h := h) _ body => "weaken " ++ h.format ++ " " ++ block (formatTreeRep body)
    | .block target body => "block " ++ formatLocal target ++ " " ++ block (formatTreeRep body)
    | .leave target value => "leave " ++ formatLocal target ++ " " ++ value.format
    | .bind name value body =>
        "let " ++ formatLocal name ++ " <- " ++ formatTreeRep value ++ line ++
          formatTreeRep body
    | .branch condition yes no =>
        "if " ++ condition.format ++ " " ++ block (formatTreeRep yes) ++
          " else " ++ block (formatTreeRep no)
    | .matchMany values rows =>
        "match " ++ group (joinSep (exprArgs values) commaLine) ++ " " ++
          block (joinSep (formatRowsRep rows) line)
    | .scoped scope body => scope.fragment.formatWith Expr.format ++ " " ++ block (formatTreeRep body)
    | .fix (sig := sig) name params body args =>
        "fix " ++ formatLocal name ++ "(" ++ group (joinSep (formatLocals params) commaLine) ++
          ") -> " ++ sig.result.format ++ " " ++ block (formatTreeRep body) ++ line ++
          application (formatLocal name) (exprArgs args)

  private def formatRowRep {types : List ObjTy} {result : ObjTy} {g : Grade} :
      RowRep types result g → Format
    | .mk patterns locals body =>
        "(" ++ group (joinSep (formatPatterns patterns locals) commaLine) ++ ") => " ++
          block (formatTreeRep body)

  private def formatRowsRep {types : List ObjTy} {result : ObjTy} {grades : List Grade} :
      RowsRep types result grades → List Format
    | .nil => []
    | .cons row rest => formatRowRep row :: formatRowsRep rest
end

public def Tree.format {g : Grade} {a : ObjTy} (tree : Tree g a) : Format :=
  private_decl% formatTreeRep tree.rep

public def Def.format {sig : Signature} (definition : Def sig) : Format :=
  let parameters := joinSep (formatLocals definition.params) commaLine
  let header := group <|
    "fn (" ++ parameters ++ ") -> " ++ sig.result.format ++ " " ++ sig.grade.format
  header ++ " " ++ block definition.body.format

public instance {sig : Signature} : ToFormat (Def sig) where
  format := Def.format

public def Def.pretty {sig : Signature} (definition : Def sig) (width : Nat) : String :=
  definition.format.pretty width

end Oria.IR.Tree
