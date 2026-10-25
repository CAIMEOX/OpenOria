module

public import Oria.Language.Persistent
public import Oria.Meta.McFunction
public import Lean.EnvExtension
meta import all Oria.Language.Persistent
meta import all Oria.Language.Builder
meta import all Oria.Meta.McFunction
meta import all Oria.Meta.McFunction.Eval
import Qq.MetaM

namespace Oria.PersistentRegistry

open Lean

private instance : Inhabited RootDefinition where
  default := ⟨⟨.anonymous, ⟨[], .unit, .pure⟩,
    IR.Tree.Def.build (fun _ => pure (.ret .unit))⟩, ⟨.anonymous⟩⟩

private initialize declarations : MapDeclarationExtension RootDefinition ← mkMapDeclarationExtension

public def find? (env : Environment) (decl : Name) : Option RootDefinition :=
  declarations.find? env decl

private def insert (env : Environment) (decl : Name) (entry : RootDefinition) : Environment :=
  declarations.insert env decl entry

end Oria.PersistentRegistry

namespace Oria.Persistent

open Lean Lean.Elab Lean.Meta Qq

private def addRoot (decl : Name) (attr : Syntax) (kind : AttributeKind) : CoreM Unit := do
  Attribute.Builtin.ensureNoArgs attr
  unless kind == .global do throwErrorAt attr "`root` requires a global declaration"
  let env ← getEnv
  let some info := env.findAsync? decl | throwErrorAt attr "unknown root declaration `{decl}`"
  let info := info.toConstantVal
  unless info.levelParams.isEmpty do
    throwErrorAt attr "root declarations require a closed type"
  let (_, registered) ← withoutModifyingEnv' do
    modifyEnv (McFunction.exposeIRForMeta · decl)
    let initial ← MetaM.run' do
      let type ← whnf info.type
      let_expr Root _ _ _ := type
        | throwErrorAt attr "a root declaration must have type `Root A`"
      let recipe ← mkAppM ``Root.initializer #[mkConst decl]
      match ← McFunction.Eval.recipe recipe with
      | .error error => throwErrorAt attr "failed to elaborate root `{decl}`: {error}"
      | .ok recipe => pure (McFunction.Internal.Recipe.compile recipe)
    unless initial.signature.args.isEmpty do
      throwErrorAt attr "a root initializer must be closed"
    unless initial.source == decl ++ `initial do
      throwErrorAt attr "use `Root.init` with the root declaration's own name"
    match ObjectRegistry.checkPersistent (← getEnv)
        (#[initial.signature.result] ++ initial.definition.dependencies.persistentTypes.toArray) with
    | .ok () => pure ()
    | .error diagnostic => throwErrorAt attr "{repr diagnostic}"
    let allowed := stateGrade.seq .failure
    unless decide (initial.signature.grade.Below allowed) do
      throwErrorAt attr "root initializers allow persistent memory and recoverable failure"
    setEnv (PersistentRegistry.insert (← getEnv) decl ⟨initial, ⟨decl⟩⟩)
  setEnv registered

initialize registerBuiltinAttribute {
  name := `root
  descr := "Register a typed persistent root and its closed initializer."
  applicationTime := .afterCompilation
  add := addRoot
}

end Oria.Persistent
