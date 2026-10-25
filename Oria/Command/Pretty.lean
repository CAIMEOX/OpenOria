module

public import Oria.Command.Syntax
public import Init.Data.Format.Basic

namespace Oria.Command

open Std
open Std.Format

private def formatApplication (name : String) (arguments : List Format) : Format :=
  match arguments with
  | [] => name
  | _ => group <| name ++ nestD (line ++ joinSep arguments ("," ++ line))

private def Segment.formatWith {v : ObjTy → Type}
    (formatValue : ∀ {a}, v a → Format) : Segment v → Format
  | Segment.token value => "token(" ++ reprStr value.text ++ ")"
  | Segment.space => "space"
  | Segment.i32 value => s!"i32({value})"
  | Segment.literal value => "literal(" ++ value.format ++ ")"
  | Segment.hole .i32 value => "hole.i32(" ++ formatValue value ++ ")"
  | Segment.hole .nativeNbt value => "hole.nativeNbt(" ++ formatValue value ++ ")"

public def Fragment.formatWith {v : ObjTy → Type}
    (formatValue : ∀ {a}, v a → Format)
    (fragment : Fragment v) : Format :=
  let segments := fragment.segments.map (Segment.formatWith formatValue)
  let encoded := formatApplication "fragment" segments
  if fragment.requirements == Req.none then
    encoded
  else
    encoded ++ s!" requires({fragment.requirements.toNat})"

private def EncodedArg.formatWith
    {v : ObjTy → Type}
    {key : SlotKey}
    (formatValue : ∀ {a}, v a → Format)
    (argument : EncodedArg v key) : Format :=
  formatApplication ("arg " ++ key.name.toString) [argument.fragment.formatWith formatValue]

private def EncodedArgs.formatsWith {v : ObjTy → Type} {schema : List SlotKey}
    (formatValue : ∀ {a}, v a → Format) : EncodedArgs v schema → List Format
  | .nil => []
  | .cons argument rest =>
      argument.formatWith formatValue :: EncodedArgs.formatsWith formatValue rest

public def Call.formatWith {v : ObjTy → Type} {sig : Signature}
    (formatValue : ∀ {a}, v a → Format)
    (request : Call v sig) : Format :=
  formatApplication ("command " ++ request.ref.key.toString)
    (request.args.formatsWith formatValue)

end Oria.Command
