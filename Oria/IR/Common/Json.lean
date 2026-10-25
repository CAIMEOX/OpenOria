module

public import Oria.IR.Common.Schema
public import Lean.Data.Json.FromToJson.Basic
import Lean.Elab.Deriving.FromToJson

namespace Oria

open Lean

public section
deriving instance ToJson for Nbt.Tag
deriving instance ToJson for Nbt.Schema
end

/- Lean's ToJson deriving handler currently misroutes nested mutual ObjTy/TypeId recursion. -/
mutual
  private def typeJson : ObjTy → Json
    | .unit => .str "unit"
    | .bool => .str "bool"
    | .i32 => .str "i32"
    | .nbt tag => Json.mkObj [("nbt", toJson tag)]
    | .nbtRef schema => Json.mkObj [("nbtRef", toJson schema)]
    | .option a => Json.mkObj [("option", typeJson a)]
    | .ref a => Json.mkObj [("ref", typeJson a)]
    | .data id => Json.mkObj [("data", idJson id)]
  termination_by a => sizeOf a

  private def idJson : TypeId → Json
    | ⟨name, args⟩ => Json.mkObj [("name", toJson name), ("args", .arr (typesJson args).toArray)]
  termination_by id => sizeOf id

  private def typesJson : List ObjTy → List Json
    | [] => []
    | a :: as => typeJson a :: typesJson as
  termination_by as => sizeOf as
end

public instance : ToJson ObjTy := private_decl% ⟨typeJson⟩
public instance : ToJson TypeId := private_decl% ⟨idJson⟩
public section
deriving instance ToJson for ReprHint
deriving instance ToJson for ConstructorSchema
deriving instance ToJson for ObjectSchema

end
end Oria
