module

public meta import Oria.Meta.ObjectDerive
public import Oria.Language.Object
meta import Lean.Elab.GuardMsgs

namespace Oria.Proofs.ObjectDeriveErrors

open Lean Lean.Elab Lean.Elab.Command

public inductive Parametric (A : Type) where
  | wrap (value : A)
  deriving Oria.Object

example : Object (Parametric Int32)
    (.data ⟨`Oria.Proofs.ObjectDeriveErrors.Parametric, [.i32]⟩) :=
  inferInstance

/--
error: Oria.Object does not support indexed inductives
-/
#guard_msgs(error, substring := true) in
public inductive Indexed (A : Type) : Nat → Type where
  | zero : Indexed A 0
  | succ : Indexed A n → Indexed A (n + 1)
  deriving Oria.Object

/--
error: Oria.Object does not support dependent proof/runtime-dependent fields
-/
#guard_msgs(error, substring := true) in
public inductive DependentField where
  | mk (value : Int32) (proof : value = value)
  deriving Oria.Object

/--
error: Oria.Object field type must be a closed first-order named type
-/
#guard_msgs(error, substring := true) in
public inductive FunctionField where
  | wrap (value : Int32 → Int32)
  deriving Oria.Object

/--
error: Oria.Object source types must inhabit Type
-/
#guard_msgs(error, substring := true) in
public inductive Large : Type 1 where
  | value
  deriving Oria.Object

/--
error: Oria.Object source types must inhabit Type
-/
#guard_msgs(error, substring := true) in
public inductive Proposition : Prop where
  | proof
  deriving Oria.Object

/--
error: Oria.Object does not support private constructors
-/
#guard_msgs(error, substring := true) in
public inductive PrivateConstructor where
  | private hidden
  deriving Oria.Object

public inductive AlreadyDerived where
  | value
  deriving Oria.Object

/--
error: Oria.Object is already derived
-/
#guard_msgs(error, substring := true) in
deriving instance Oria.Object for AlreadyDerived

public inductive Preoccupied where
  | value

namespace Preoccupied.Oria

public def code : Nat := 0

end Preoccupied.Oria

/--
error: Oria.Object generated declaration Preoccupied.Oria.code already exists
-/
#guard_msgs(error, substring := true) in
deriving instance Oria.Object for Preoccupied

end Oria.Proofs.ObjectDeriveErrors
