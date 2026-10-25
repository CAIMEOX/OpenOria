module

public import Oria.Command.Syntax
public import Oria.Nbt.Syntax

namespace Oria.Command.Fragment

/-- Static NBT leaves and typed holes share the existing fragment algebra. -/
@[expose] public def nbtList {v : ObjTy → Type} (values : List (Fragment v)) : Fragment v :=
  append (token "[") <| append
    ((values.intersperse (.token ",")).foldl append empty) (token "]")

@[expose] public def nbtCompound {v : ObjTy → Type} (fields : List (Nbt.Key × Fragment v)) : Fragment v :=
  let values := fields.map fun (key, value) =>
    append (nbt (.string key.text)) (append (token ":") value)
  append (token "{") <| append
    ((values.intersperse (.token ",")).foldl append empty) (token "}")

end Oria.Command.Fragment
