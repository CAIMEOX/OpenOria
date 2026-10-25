module

import Oria.Examples.RoundLedger

namespace Oria.Proofs.LanguageExample

open Oria Oria.Examples.RoundLedger

-- These equations check the inferred public contracts. Observable command behavior is
-- exercised separately by the native language acceptance suite.
example : records.signature.grade = ⟨Req.none, Eff.scoreboardWrite⟩ := rfl

example : snapshot.signature.grade = Persistent.readGrade.seq ⟨Req.none, Eff.scoreboardWrite⟩ := rfl

example : reset.signature.grade = Persistent.allocGrade.seq Persistent.writeGrade := rfl

example : round.signature.grade = Persistent.stateGrade.seq readWrite.handled := rfl

example : control.signature.grade = readWrite.handled := rfl

example : selection.signature.grade = readWrite.handled := rfl

example : recovery.signature.grade = readWrite.handled := rfl

example : batch.signature.grade = readWrite.handled := rfl

example : emptyBatch.signature.grade = readWrite.handled := rfl

end Oria.Proofs.LanguageExample
