module

namespace Oria.Datapack

/-- The Minecraft data-pack contract selected by this compiler. -/
public inductive Version where
  | dp121
  deriving BEq, DecidableEq, Hashable, Repr

namespace Version

/-- Minecraft's major and minor data-pack version. -/
@[expose] public def dataPackVersion : Version → Nat × Nat
  | .dp121 => (121, 0)

@[simp] public theorem dataPackVersion_dp121 :
    dataPackVersion .dp121 = (121, 0) := rfl

end Version

end Oria.Datapack
