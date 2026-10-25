module

public meta import Oria.Meta.ObjectDerive

public import Oria.Language.Object

namespace Oria.Proofs.Fixtures

public inductive MaybeI32 where
  | none
  | some (value : Int32)
  deriving Oria.Object

public inductive Choice where
  | rock
  | paper
  | scissors
  deriving Oria.Object

public inductive Naming where
  | objectId
  | foo
  | fooDesc
  | elim
  deriving Oria.Object

public abbrev AliasI32 := Int32

public inductive Aliased where
  | wrap (value : AliasI32)
  deriving Oria.Object

public structure Token where
  deriving Oria.Object

public inductive TwoPayload where
  | left (value : Int32)
  | right (value : Int32)
  deriving Oria.Object

end Oria.Proofs.Fixtures
