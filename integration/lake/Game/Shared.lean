module

public import Oria
meta import Oria

namespace Game

@[mcfunction]
public def increment (n : Oria.Val Int32) : Oria.Prog .pure Int32 :=
  Oria.Prog.pure (n + 1)
