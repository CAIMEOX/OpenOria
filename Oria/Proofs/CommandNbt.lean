module

import Oria.Command.Nbt
import Oria.IR.DP121.Pretty
meta import Oria.Command.Nbt
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.CommandNbt

open Oria.Command Oria.Target.DP121

private def key : SlotKey := ⟨`proof.nbt⟩
private def sig : Oria.Command.Signature := ⟨[key], Req.none, Eff.none⟩
private def ref : Oria.Command.Ref sig :=
  ⟨`proof.nbt, ⟨[.token (.ofString "probe"), .space, .slot ⟨0, by decide⟩]⟩, none⟩

private def plan (fragment : Fragment (fun _ => Int32)) := do
  let catalog ← Catalog.build [ref.declaration]
  planWithCatalog catalog (ref.call (.cons ⟨fragment⟩ .nil))

private def rendered (fragment : Fragment (fun _ => Int32)) : Except Diagnostic (String × Nat) := do
  let p ← plan fragment
  p.withInvocation
    (fun i => pure ((Oria.Target.DP121.Command.invoke i).format.pretty 120, 0))
    (fun schema _ _ i _ => pure ((Oria.Target.DP121.Command.invoke i).format.pretty 120, schema.fields.length))

#guard (rendered (.nbt (nbt% {text: "Hello $(literal)"}))).toOption =
  some ("probe {\"text\":\"Hello \\u0024(literal)\"}", 0)

private def mixed : Fragment (fun _ => Int32) :=
  .nbtCompound [(⟨"fixed"⟩, .nbt (nbt% "text")), (⟨"value"⟩, .hole .i32 7)]

#guard (rendered mixed).toOption = some ("probe {\"fixed\":\"text\",\"value\":$(p0)}", 1)
example : mixed.holeCount = 1 := rfl
example {v : ObjTy → Type} (f : Fragment v) : f.map (fun x => x) = f := Fragment.map_id f
example (id : ResourceId) : SyntaxToken.Valid (SyntaxToken.ofResourceId id).text :=
  (SyntaxToken.ofResourceId id).valid

#guard !(plan (.nbt (Nbt.Value.float (1 / 0)))).isOk
#guard (Inline.parse "@a[name=\"round one\"]").isOk
#guard !(Inline.parse "@a\nsay injected").isOk
#guard !(Inline.parse "@a[tag=$(unknown)]").isOk

end Oria.Proofs.CommandNbt
