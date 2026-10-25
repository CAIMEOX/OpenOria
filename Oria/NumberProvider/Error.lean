module

namespace Oria.NumberProvider

/-- A provider encoding error, independent of the object-program compiler. -/
public inductive Error where
  | intConstantOutOfRange (value : Int)
  | nonFiniteFloatConstant (value : String)
  deriving BEq, DecidableEq, Repr

end Oria.NumberProvider
