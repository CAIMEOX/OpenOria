module

import Oria.Std.Execute
import Oria.Effect.Labels

namespace Oria.Proofs.ExecuteSyntax

open Oria.Execute

private def forward : Scope (fun _ => Int32) := Scope.ofSteps [.as .allPlayers, .at .self]
private def reverse : Scope (fun _ => Int32) := Scope.ofSteps [.at .self, .as .allPlayers]

example : forward.change.apply Req.executor = Req.none := rfl
example : reverse.change.apply Req.executor = Req.executor := rfl
example : forward.change.give = Req.executor ||| Req.position ||| Req.rotation ||| Req.dimension := rfl
example : (Kind.positioned.change).give = Req.position ||| Req.anchor := rfl
example : (Kind.positionedAs.change).give = Req.position := rfl
example : (Kind.positionedOver.change).give = Req.position := rfl
example : (Kind.onEntity.change).apply Req.position = Req.executor ||| Req.position := rfl
example : (Kind.summon.change).apply Req.executor = Req.position ||| Req.dimension := rfl
example : (Kind.storeResult .nbt).effects = Eff.world := rfl
example : (Kind.storeSuccess .bossbar).effects = Eff.world ||| Eff.hud := rfl
example : (Kind.storeSuccess .nbt).capturesSuccess = true := rfl
example : (Kind.storeSuccess .nbt).capturesResult = false := rfl
example : (Kind.storeResult .bossbar).capturesResult = true := rfl
example : (Scope.ofSteps (v := EncodedVal) [
    .storeSuccess (.nbt (.storage "demo:state") (.key "ok") .byte (.static 1))]).grade .pure =
      ⟨Req.none, Eff.world⟩ := rfl
example {v w : ObjTy → Type} (scope : Scope v) (f : ∀ {a}, v a → w a) (g : Grade) :
    (scope.map f).grade g = scope.grade g := rfl

end Oria.Proofs.ExecuteSyntax
