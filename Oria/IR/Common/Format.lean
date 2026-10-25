module

public import Oria.IR.Common.Signature
public import Oria.IR.Common.Memory
public import Oria.Command.Pretty
public import Init.Data.Format.Basic

namespace Oria

open Std Std.Format

private def applied (name : String) (args : List Format) : Format :=
  if args.isEmpty then name
  else group (name ++ "[" ++ nest 2 (joinSep args ("," ++ line)) ++ "]")

mutual
  private def formatType : ObjTy → Format
    | .unit => "Unit"
    | .bool => "Bool"
    | .i32 => "I32"
    | .nbt t => applied "Nbt" [repr t]
    | .nbtRef s => applied "NbtRef" [repr s]
    | .option a => applied "Option" [formatType a]
    | .ref a => applied "Ref" [formatType a]
    | .data id => formatId id
  termination_by a => sizeOf a

  private def formatId : TypeId → Format
    | ⟨name, args⟩ => applied name.toString (formatTypes args)
  termination_by id => sizeOf id

  private def formatTypes : List ObjTy → List Format
    | [] => []
    | a :: as => formatType a :: formatTypes as
  termination_by as => sizeOf as
end

public def ObjTy.format (a : ObjTy) : Format := private_decl% formatType a

public def Grade.format (grade : Grade) : Format :=
  "!{" ++ s!"req={grade.req.toNat}, eff={grade.eff.toNat}" ++ "}"

private def nbtFragment {as : List ObjTy} (fragment : IR.Nbt.Fragment as) : Format :=
  fragment.formatWith (fun x => "$" ++ toString x.index.val)

private def nbtPath {as : List ObjTy} (path : IR.Nbt.Path (IR.Scope.Var Unit as .i32)) : Format :=
  group (join (path.segments.map fun
    | .key key => ("." : Format) ++ key.format
    | .index i => "[$" ++ toString i.index.val ++ "]"
    | .all => "[]"
    | .matching impossible => nomatch impossible) ++
    if path.check == .available then (" {present}" : Format) else nil)

private def nbtWrite {as : List ObjTy} : IR.Nbt.Write (IR.Scope.Var Unit as .i32) → Format
  | .literal value => value.2.formatSnbt
  | .i32 value => "$" ++ toString value.index.val

private def nbtBase {as : List ObjTy} : IR.Nbt.Base as → Format
  | .arena root => "$" ++ toString root.index.val
  | .global ref => group ("storage " ++ ref.storage.render ++ nest 2 (line ++ ref.path.format))

private def nbtSource {as : List ObjTy} : IR.Nbt.Source as → Format
  | .external target path => group (nbtFragment target ++ nest 2
      (join (path.toList.map fun path => line ++ nbtFragment path)))
  | .value value path => group ("$" ++ toString value.index.val ++ nest 2
      (join (path.toList.map fun path => line ++ nbtFragment path)))
  | .reference base path => nbtBase base ++ nbtPath path

public def IR.MemoryOp.format {g : Grade} {as : List ObjTy} {a : ObjTy} : IR.MemoryOp g as a → Format
  | .nbt op => match op with
      | .newRef _ value => "nbt.alloc " ++ value.2.formatSnbt
      | .inspectRef base path true => "nbt.readI32 " ++ nbtBase base ++ nbtPath path
      | .inspectRef base path false => "nbt.length " ++ nbtBase base ++ nbtPath path
      | .inspectValue _ path _ => "nbt.measure " ++ nbtFragment path
      | .putRef base path value isAppend => group
          ((if isAppend then "nbt.append " else "nbt.set ") ++ nbtBase base ++ nbtPath path ++
            nest 2 (line ++ nbtWrite value))
      | .clearRef base path => "nbt.clear " ++ nbtBase base ++ nbtPath path
      | .copyRef a dst b src _ => "nbt.copy " ++ nbtBase a ++ nbtPath dst ++ " " ++ nbtBase b ++ nbtPath src
      | .exportRef _ _ target path => "nbt.export " ++ nbtFragment target ++ " " ++ nbtFragment path
      | .literal value => "nbt.literal " ++ value.formatSnbt
      | .integer => "nbt.integer"
      | .forget => "nbt.forget"
      | .number => "nbt.number"
      | .read .one source => "nbt.readOne " ++ nbtSource source
      | .read .all source => "nbt.readAll " ++ nbtSource source
      | .write target path value => group ("nbt.write " ++ nbtFragment target ++
          nest 2 (line ++ nbtFragment path ++ line ++ "$" ++ toString value.index.val))
  | .persist => "persist"
  | .rootGet ref => "root.get " ++ ref.name.toString
  | .rootSet ref => "root.set " ++ ref.name.toString
  | .refNew => "ref.new"
  | .refGet => "ref.get"
  | .refSet => "ref.set"

end Oria
