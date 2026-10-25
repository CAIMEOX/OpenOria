module

public import Oria.Compiler.Definition
public import Oria.IR.Program.Closed

namespace Oria.Compiler

open Oria Oria.IR Oria.Program

/-- Whole-program provenance for the bodies retained by a closed program. -/
public structure ProgramCertificate (closed : Program.ClosedProgram) : Prop where
  everyMemberCompiled :
    ∀ member ∈ closed.members.toList,
      Compiler.compile closed.collected.functions closed.collected.objects
          closed.collected.commands member.origin.definition =
        .ok (member.signatureCorrect ▸ member.body)

/-- A closed program together with the compiler provenance that produced it. -/
public structure CompiledProgram where
  closed : Program.ClosedProgram
  certificate : ProgramCertificate closed

end Oria.Compiler
