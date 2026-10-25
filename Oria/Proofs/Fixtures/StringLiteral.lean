module

public meta import Oria.Data.StringLiteral

namespace Oria.Proofs.Fixtures.StringLiteral

public structure Name where
  text : String
  nonempty : text ≠ "" := by decide

public def Name.ofString (s : String) (h : s ≠ "" := by decide) : Name := ⟨s, h⟩

attribute [string_literal Name.ofString] Name

end Oria.Proofs.Fixtures.StringLiteral
