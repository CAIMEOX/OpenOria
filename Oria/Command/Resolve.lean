module

public import Oria.Datapack.Version
public import Oria.Command.Catalog

namespace Oria.Datapack.Version

/-- Resolve a typed request through the catalogue supplied by the selected target entry point. -/
public def resolveRef {sig : Command.Signature}
    (version : Version) (catalog : Command.Catalog) (ref : Command.Ref sig) :
    Except Diagnostic <| PLift <|
      Command.Catalog.ResolvesRef catalog ref := do
  match version with
  | .dp121 =>
      let resolved ← catalog.resolveRef ref
      pure ⟨resolved.sound⟩

/-- Resolve a typed call through its command reference. -/
public def resolve {f : ObjTy → Type} {sig : Command.Signature}
    (version : Version) (catalog : Command.Catalog) (request : Command.Call f sig) :
    Except Diagnostic <| PLift <|
      Command.Catalog.Resolves catalog request :=
  version.resolveRef catalog request.ref

end Oria.Datapack.Version
