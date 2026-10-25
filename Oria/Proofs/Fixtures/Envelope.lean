module

public meta import Oria.Meta.ObjectDerive

public import Oria.Proofs.Fixtures.MaybeI32

namespace Oria.Proofs.Fixtures

public inductive Envelope where
  | wrap (payload : MaybeI32)
  deriving Oria.Object

end Oria.Proofs.Fixtures
