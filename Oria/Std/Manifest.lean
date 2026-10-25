module

public import Oria.Command.Catalog
public import Oria.Std.Command.Declarations

set_option doc.verso true
set_option doc.verso.module false
set_option linter.missingDocs true

/-!
# Standard command catalog

Compiler tools obtain the standard command catalog through this module and can add custom
declarations using the same catalog interface. Object programs import [Oria.Std](##Oria.Std).
-/

namespace Oria.Std.Manifest

/-- Command declarations provided by the Oria standard library. -/
@[expose] public def commandDeclarations : List Oria.Command.Decl :=
  Oria.Std.Command.Declarations.all

/-- Check the standard declarations and build a catalog, reporting errors such as duplicate identities. -/
@[expose] public def commandCatalog :
    Except Oria.Diagnostic Oria.Command.Catalog :=
  Oria.Command.Catalog.build commandDeclarations

end Oria.Std.Manifest
