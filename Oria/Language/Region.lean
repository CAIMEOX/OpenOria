module

namespace Oria

/-- A type-level guarantee carried by a value and erased from the object calling convention. -/
public abbrev Region := Type

namespace Region

/-- A value usable within the current ordinary entry, including either arena. -/
public inductive any

/-- A value whose reachable pointer graph belongs to the persistent arena. -/
public inductive persistent

end Region

end Oria
