module

import Oria.Proofs.Fixtures.MaybeI32

namespace Oria.Proofs.SourceTypes

open Oria
open Oria.IR
open Oria.Proofs.Fixtures

example : Object MaybeI32 MaybeI32.Oria.code := inferInstance

example : Prog .pure MaybeI32 :=
  MaybeI32.Obj.Ctor.none

example (v : Val Int32) : Prog .pure MaybeI32 :=
  MaybeI32.Obj.Ctor.some v

end Oria.Proofs.SourceTypes
