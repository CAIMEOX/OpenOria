module

import Oria
import Oria.Std.Dialog
import Oria.Std.Command.Declarations
import Oria.Std.DP121
import Oria.IR.DP121.Pretty
meta import Oria
meta import Oria.Std.Dialog
meta import Oria.Std.DP121
meta import Oria.IR.DP121.Pretty

namespace Oria.Proofs.StdDialog

open Oria.Std Oria.Std.Command.Arg

@[mcfunction]
private def showNotice : Prog (Dialog.grade Players.all) Int32 :=
  Dialog.notice .all "Oria" "Welcome"

@[mcfunction]
private def showNamed : Prog (Dialog.grade Players.self Req.all) Int32 := do
  Dialog.show .self (.named (.ofString "minecraft:server_links"))

private def dynamicContent (n : Val Int32) : DialogContent :=
  .inline <| .nbtCompound [
    (⟨"type"⟩, .nbt (.string "minecraft:notice")),
    (⟨"title"⟩, .nbt (.string "Score")),
    (⟨"body"⟩, .nbtCompound [
      (⟨"type"⟩, .nbt (.string "minecraft:plain_message")),
      (⟨"contents"⟩, .nbtCompound [
        (⟨"translate"⟩, .nbt (.string "%s")),
        (⟨"with"⟩, .nbtList [.hole .i32 n])])])]

@[mcfunction]
private def showDynamic (n : Val Int32) : Prog (Dialog.grade Players.self Req.all) Int32 := by
  simpa [Dialog.grade, dynamicContent, Oria.Command.encode,
    Oria.Command.ArgCodec.encode, Oria.Command.Call.grade,
    Oria.Command.Call.requirements, Oria.Command.EncodedArgs.requirements,
    Oria.Command.EncodedArg.requirements, Oria.Command.Ref.call, Args.foldl,
    Oria.Command.Fragment.requirements, Oria.Command.Fragment.nbtCompound,
    Oria.Command.Fragment.nbtList, Oria.Command.Fragment.nbt,
    Oria.Command.Fragment.hole, Oria.Command.Fragment.append,
    Oria.Command.Fragment.spaced, Req.none, BitVec.or_assoc] using
    (Dialog.show .self (dynamicContent n))

example : showNotice.signature.grade = Dialog.grade Players.all := rfl
example : showNamed.signature.grade = Dialog.grade Players.self Req.all := rfl
example : showDynamic.signature.grade = Dialog.grade Players.self Req.all := rfl
example : Grade.Below ⟨Req.none, Eff.dialog⟩ (Dialog.grade Players.all) := by decide
example : showNotice.signature.grade.req = Req.none := rfl
example : showNotice.signature.grade.req ||| Req.server = Req.server := by decide
example : ¬(showNamed.signature.grade.req ||| Req.server = Req.server) := by decide
example : Prog (Dialog.clearGrade Players.all) Int32 := Dialog.clear .all
example : Prog (Dialog.grade Players.all Req.all) Int32 := by
  simpa [DialogContent.ofNbt_requirements] using
    Dialog.show .all (.ofNbt (nbt% {type: "minecraft:confirmation", title: "Continue?",
      yes: {label: "Yes"}, no: {label: "No"}}))

private def rendered {sig : Command.Signature}
    (request : Command.Call EncodedVal sig) : Except Diagnostic (String × Nat) := do
  let plan ← Std.DP121.plan request
  plan.withInvocation
    (fun i => pure ((Target.DP121.Command.invoke i).format.pretty 120, 0))
    (fun schema _ _ i _ => pure ((Target.DP121.Command.invoke i).format.pretty 120, schema.fields.length))

private def named := Std.Command.Declarations.dialogShow.call <|
  .cons (Command.encode Players.all) <|
  .cons (Command.encode (DialogContent.named (.ofString "minecraft:server_links"))) .nil

private def clear := Std.Command.Declarations.dialogClear.call <|
  .cons (Command.encode Players.all) .nil

#guard (rendered named).toOption = some ("dialog show @a minecraft:server_links", 0)
#guard (rendered clear).toOption = some ("dialog clear @a", 0)

end Oria.Proofs.StdDialog
