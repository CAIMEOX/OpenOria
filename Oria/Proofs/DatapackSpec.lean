module

import Oria.Datapack.Spec
meta import Oria.Datapack.Spec

namespace Oria.Proofs.DatapackSpec

open Oria Oria.IR Oria.Datapack

private def root : DeclRef ⟨[], .unit, .pure⟩ := .named `root

private def spec : Spec :=
  build { ns := .ofString "oria" } do
    entry (.ofString "main") root
    onLoad root
    onLoad root
    onTick root

example (r : Registration) : r.reference.sig.args = [] := r.arguments_empty
example (r : Registration) : r.reference.sig.result = .unit := r.result_unit

#guard spec.settings.version == .dp121
#guard spec.roots.size == 4
#guard spec.check.isOk
#guard (build { ns := .ofString "oria" } (pure ())).check.isOk

#guard
  match (build { ns := .ofString "oria" } do
      entry (.ofString "main") root
      entry (.ofString "main") root).check with
  | .error (.duplicatePublicFunctionPath "main") => true
  | _ => false

end Oria.Proofs.DatapackSpec
