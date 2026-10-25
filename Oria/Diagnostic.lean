module

public import Oria.IR.Common.Type
public import Oria.Effect.Grade
public import Oria.IR.Common.Signature

namespace Oria

public inductive RepresentationLocation where
  | parameter (index : Nat)
  | result
  | body
  deriving BEq, DecidableEq, Repr

/-- Why a nominal Tree local cannot denote one exact lexical binding. -/
public inductive LocalScopeFailure where
  | unbound
  | ambiguous
  deriving BEq, DecidableEq, Repr

public inductive Diagnostic where
  | duplicateObjectType (id : TypeId)
  | invalidObjectSchema (id : TypeId)
  | unresolvedObjectType (owner missing : TypeId)
  | unknownObjectType (id : TypeId)
  | persistentLayoutTooWide (type : ObjTy) (slots : Nat)
  | mutableNbtPersistence
  | invalidValueType (id : TypeId)
  | recursiveValueType (id : TypeId)
  | pointerValueField (owner : TypeId) (field : ObjTy)
  | unknownRoot (name : Lean.Name)
  | rootTypeMismatch (name : Lean.Name) (expected actual : ObjTy)
  | invalidRootInitializer (name : Lean.Name)
  | duplicatePersistentRoot (name : Lean.Name)
  | unknownNbtGlobal (storage path : String)
  | reservedNbtGlobal (storage : String)
  | overlappingNbtGlobals (storage : String)
  | unknownConstructor (owner : TypeId) (name : Lean.Name)
  | constructorShapeMismatch
      (owner : TypeId)
      (name : Lean.Name)
      (expected actual : List ObjTy)
  | nonExhaustiveMatch (definition : Lean.Name)
  | redundantPattern (definition : Lean.Name) (row : Nat)
  | duplicateCommand (key : Lean.Name)
  | invalidCommandTemplate (key : Lean.Name)
  | unknownCommand (key : Lean.Name)
  | commandSignatureMismatch (key : Lean.Name)
  | commandTemplateMismatch (key : Lean.Name)
  | invalidCommandName (name : String)
  | invalidCommandToken (token : String)
  | invalidCommandText (text : String)
  | invalidCommandNbt (reason : String)
  | invalidResourceId (id : String)
  | duplicatePublicFunctionPath (path : String)
  | unresolvedTargetFunction (name : String)
  | artifactPathConflict (path : String)
  | unknownMcFunction (name : Lean.Name)
  | invalidMcFunctionEntry (name : Lean.Name)
  | duplicateFunction (name : Lean.Name)
  | unloweredRecursion
  | unsupportedRepresentation
      (definition : Lean.Name)
      (type : ObjTy)
      (location : RepresentationLocation)
  | unknownFunction (name : Lean.Name)
  | functionSignatureMismatch
      (name : Lean.Name)
      (expected actual : Signature)
  | invalidLocalScope
      (definition : Lean.Name)
      (type : ObjTy)
      (failure : LocalScopeFailure)
  | unsupportedMachineLowering (definition : Lean.Name)
  | invalidRegisterBudget (budget : Nat)
  | invalidRegisterAllocation (definition : Lean.Name)
  | invalidParallelTransfer
  | invalidTask (reason : String)
  | unboundedTaskRegion (function : String)
  | taskBudgetTooSmall (configured required : Nat)
  deriving BEq, DecidableEq, Repr

end Oria
