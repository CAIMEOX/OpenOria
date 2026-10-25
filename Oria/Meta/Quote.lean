module

public import Oria.IR.Common.Type
public import Lean.ToExpr
import Lean.Elab.Deriving.ToExpr

public section

namespace Oria

open Lean

deriving instance ToExpr for Nbt.Tag
deriving instance ToExpr for Nbt.Schema

instance : Quote Nbt.Tag where
  quote t := mkCIdent (match t with
    | .byte => ``Nbt.Tag.byte | .short => ``Nbt.Tag.short | .int => ``Nbt.Tag.int
    | .long => ``Nbt.Tag.long | .float => ``Nbt.Tag.float | .double => ``Nbt.Tag.double
    | .string => ``Nbt.Tag.string | .byteArray => ``Nbt.Tag.byteArray
    | .intArray => ``Nbt.Tag.intArray | .longArray => ``Nbt.Tag.longArray
    | .list => ``Nbt.Tag.list | .compound => ``Nbt.Tag.compound)

/-- Absolute Option constructors distinguish host tag knowledge from object Option builders. -/
def quoteNbtTag : Option Nbt.Tag → Term
  | none => mkCIdent ``_root_.Option.none
  | some t => Syntax.mkCApp ``_root_.Option.some #[quote t]

private partial def quoteSchema : Nbt.Schema → Term
  | .atom t => Syntax.mkCApp ``Nbt.Schema.atom #[quote t]
  | .boolean => mkCIdent ``Nbt.Schema.boolean
  | .enumeration xs => Syntax.mkCApp ``Nbt.Schema.enumeration #[quote xs]
  | .list s => Syntax.mkCApp ``Nbt.Schema.list #[quoteSchema s]
  | .record fs => Syntax.mkCApp ``Nbt.Schema.record #[quote (fs.map fun p => (p.1, quoteSchema p.2))]
  | .variant cs => Syntax.mkCApp ``Nbt.Schema.variant #[quote (cs.map fun p => (p.1, p.2.map quoteSchema))]

instance : Quote Nbt.Schema where quote := private_decl% quoteSchema

deriving instance ToExpr for TypeId
deriving instance ToExpr for ObjTy

mutual
  private def quoteType : ObjTy → Term
    | .unit => mkCIdent ``ObjTy.unit
    | .bool => mkCIdent ``ObjTy.bool
    | .i32 => mkCIdent ``ObjTy.i32
    | .nbt tag => Syntax.mkCApp ``ObjTy.nbt #[quoteNbtTag tag]
    | .nbtRef schema => Syntax.mkCApp ``ObjTy.nbtRef #[quote schema]
    | .option a => Syntax.mkCApp ``ObjTy.option #[quoteType a]
    | .ref a => Syntax.mkCApp ``ObjTy.ref #[quoteType a]
    | .data id => Syntax.mkCApp ``ObjTy.data #[quoteId id]
  termination_by t => sizeOf t

  private def quoteId : TypeId → Term
    | ⟨name, args⟩ => Syntax.mkCApp ``TypeId.mk #[quote name, quoteTypes args]
  termination_by id => sizeOf id

  private def quoteTypes : List ObjTy → Term
    | [] => mkCIdent ``List.nil
    | a :: rest => Syntax.mkCApp ``List.cons #[quoteType a, quoteTypes rest]
  termination_by xs => sizeOf xs
end

instance : Quote ObjTy where quote := private_decl% quoteType
instance : Quote TypeId where quote := private_decl% quoteId

end Oria
