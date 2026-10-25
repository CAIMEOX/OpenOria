module

public import Oria.Nbt.Decode
public import Oria.Nbt.Format

namespace Oria.Nbt

open Std

private def tagName : Tag → Format
  | .byte => "byte" | .short => "short" | .int => "int" | .long => "long"
  | .float => "float" | .double => "double" | .string => "string"
  | .byteArray => "byte array" | .intArray => "int array" | .longArray => "long array"
  | .list => "list" | .compound => "compound"

public def DecodeIssue.format : DecodeIssue → Format
  | .tag expected actual => "expected " ++ tagName expected ++ ", got " ++ tagName actual
  | .missingField => "missing field"
  | .unknownConstructor name => "unknown constructor " ++ (Key.mk name).format
  | .constructorKeys count => "expected one constructor key, got " ++ toString count
  | .arity expected actual =>
      "expected " ++ toString expected ++ " constructor arguments, got " ++ toString actual
  | .boolean value => "expected 0b or 1b, got " ++ toString value ++ "b"

public def DecodeError.format (error : DecodeError) : Format :=
  Format.group (formatSuffix "$" error.path ++ ":" ++ Format.nest 2 (Format.line ++ error.reason.format))

public def DecodeError.pretty (error : DecodeError) (width : Nat) : String :=
  error.format.pretty width

end Oria.Nbt
