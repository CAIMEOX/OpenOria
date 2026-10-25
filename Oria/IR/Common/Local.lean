module

public import Oria.IR.Common.Type

namespace Oria.IR

/-- Shared typed lexical identity. Ordinary imports cannot inspect or mint locals. -/
public structure Local {α : Type} (a : α) where
  private mk ::
  private serial : Nat
  deriving BEq, DecidableEq, Hashable

/-- Trusted compiler modules import all of this module to mint locals from a private supply. -/
private def Local.fresh {α : Type} {a : α} (serial : Nat) : Local a :=
  ⟨serial⟩

end Oria.IR
