module

public import Oria.IR.Common.Reference

namespace Oria.IR.Tree

mutual
  /-- A pattern indexed by its subject and its ordered binder telescope. -/
  public inductive Pattern : ObjTy → List ObjTy → Type where
    | any {a : ObjTy} : Pattern a []
    | bind {a : ObjTy} : Pattern a [a]
    | i32 : Int32 → Pattern .i32 []
    | ctor {a : ObjTy} {fields : List ObjTy} {bindings : List ObjTy} :
        Constructor a fields → Patterns fields bindings → Pattern a bindings

  /-- Simultaneous patterns concatenate their binder telescopes in source order. -/
  public inductive Patterns : List ObjTy → List ObjTy → Type where
    | nil : Patterns [] []
    | cons {a : ObjTy} {bindings : List ObjTy} {types : List ObjTy} {rest : List ObjTy} :
        Pattern a bindings → Patterns types rest →
        Patterns (a :: types) (bindings ++ rest)
end

namespace Patterns

public def append {types : List ObjTy} {bindings : List ObjTy} {more : List ObjTy} {rest : List ObjTy}
    (left : Patterns types bindings) (right : Patterns more rest) :
    Patterns (types ++ more) (bindings ++ rest) :=
  match left with
  | .nil => right
  | .cons head tail => by
      simpa only [List.append_assoc, List.cons_append] using Patterns.cons head (append tail right)

public def ignoreAll : (types : List ObjTy) → Patterns types []
  | [] => .nil
  | _ :: types => .cons .any (ignoreAll types)

public def bindAll : (types : List ObjTy) → Patterns types types
  | [] => .nil
  | _ :: types => .cons .bind (bindAll types)

end Patterns

end Oria.IR.Tree
