module

public import Oria
meta import Oria

namespace Oria.Proofs.Fixtures.PersistentRoot

open Oria.Persistent

@[root]
public def points : Root Int32 := Root.init (persist 0)

end Oria.Proofs.Fixtures.PersistentRoot
