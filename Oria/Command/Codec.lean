module

public import Oria.Language.Builder
public import Oria.Command.Syntax

namespace Oria.Command

universe u

/-- Encode a source argument as a command fragment with typed dynamic values. -/
public class ArgCodec (A : Type u) where
  key : SlotKey
  encode : A → Fragment EncodedVal

@[expose] public def encode {A : Type u} [codec : ArgCodec A]
    (argument : A) : EncodedArg EncodedVal codec.key :=
  ⟨codec.encode argument⟩

end Oria.Command
