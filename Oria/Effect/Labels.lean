module

public import Oria.Effect.Grade

namespace Oria

namespace Req

@[expose] public def none : ReqRow := 0#8
@[expose] public def executor : ReqRow := 1#8
@[expose] public def position : ReqRow := 2#8
@[expose] public def rotation : ReqRow := 4#8
@[expose] public def dimension : ReqRow := 8#8
@[expose] public def anchor : ReqRow := 16#8
@[expose] public def all : ReqRow := 31#8
@[expose] public def server : ReqRow := 30#8

end Req

namespace Eff

@[expose] public def failure : EffRow := Grade.failure.eff
@[expose] public def suspend : EffRow := Grade.suspension.eff

@[expose] public def none : EffRow := 0#16
@[expose] public def world : EffRow := 1#16
@[expose] public def scoreboardRead : EffRow := 2#16
@[expose] public def scoreboardWrite : EffRow := 4#16
@[expose] public def persistentRead : EffRow := 8#16
@[expose] public def persistentWrite : EffRow := 16#16
@[expose] public def persistentAlloc : EffRow := 32#16
@[expose] public def random : EffRow := 64#16
@[expose] public def chat : EffRow := 128#16
@[expose] public def dialog : EffRow := 256#16
@[expose] public def sound : EffRow := 512#16
@[expose] public def hud : EffRow := 1024#16
@[expose] public def memoryRead : EffRow := 8192#16
@[expose] public def memoryWrite : EffRow := 16384#16

end Eff

end Oria
