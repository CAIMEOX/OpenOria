module

public import Oria.Command.Syntax

namespace Oria.Command

/-- Native inclusive range syntax, shared by selectors and command arguments. -/
public inductive Range (a : Type) where
  /-- A single value. -/
  | exact : a → Range a
  /-- Lower and upper bounds, inclusive. -/
  | between : a → a → Range a
  /-- Inclusive lower bound. -/
  | atLeast : a → Range a
  /-- Inclusive upper bound. -/
  | atMost : a → Range a
  /-- Unbounded syntax, subject to the receiving command's grammar. -/
  | any

/-- Encode range punctuation once while delegating each bound to its numeric codec. -/
@[expose] public def Range.fragment {a : Type} {v : ObjTy → Type}
    (encode : a → Fragment v) : Range a → Fragment v
  | .exact n => encode n
  | .between lo hi => (encode lo).append ((Fragment.token "..").append (encode hi))
  | .atLeast lo => (encode lo).append (.token "..")
  | .atMost hi => .prepend ".." (encode hi)
  | .any => .token ".."

end Oria.Command
