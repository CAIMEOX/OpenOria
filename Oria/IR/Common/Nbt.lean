module

public import Oria.Command.Syntax
public import Oria.IR.Common.Scope
public import Oria.IR.Common.Nbt.Path
public import Oria.IR.Common.Nbt.Global

namespace Oria.IR.Nbt

public inductive ReadMode where
  | one
  | all
  deriving BEq, DecidableEq, Repr

@[expose] public def ReadMode.tag : ReadMode → Option Oria.Nbt.Tag
  | .one => none
  | .all => some .list

/-- Static command syntax whose dynamic holes refer to the operation's operand telescope. -/
public abbrev Fragment (as : List ObjTy) := Command.Fragment (Scope.Var Unit as)

@[expose] public def readGrade : Grade := ⟨Req.none, Eff.memoryRead ||| Eff.failure⟩
@[expose] public def writeGrade : Grade := ⟨Req.none, Eff.memoryWrite ||| Eff.failure⟩
@[expose] public def copyGrade : Grade := readGrade.seq writeGrade

/-- Address sources for schema-directed mutable documents. Global addresses have no runtime word. -/
public inductive Base (as : List ObjTy) where
  | arena {s : Oria.Nbt.Schema} : Scope.Var Unit as (.nbtRef s) → Base as
  | global : GlobalRef → Base as

@[expose] public def Base.rename {as bs : List ObjTy} (ρ : Scope.Renaming Unit Unit as bs) :
    Base as → Base bs
  | .arena root => .arena (ρ root)
  | .global ref => .global ref

public def Base.globals {as : List ObjTy} : Base as → Array GlobalRef
  | .arena _ => #[]
  | .global ref => #[ref]

/-- A native NBT selection. Local paths include their leading field separator when needed. -/
public inductive Source (as : List ObjTy) where
  | external : Fragment as → Option (Fragment as) → Source as
  | value {t : Option Oria.Nbt.Tag} : Scope.Var Unit as (.nbt t) →
      Option (Fragment as) → Source as
  | reference : Base as → Path (Scope.Var Unit as .i32) → Source as

@[expose] public def Source.grade {as : List ObjTy} : Source as → Grade
  | .external target path =>
      ⟨target.requirements ||| (path.map (·.requirements)).getD Req.none,
        Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩
  | .value _ path => ⟨(path.map (·.requirements)).getD Req.none, Eff.failure⟩
  | .reference _ _ => readGrade

/-- Native snapshots and typed mutable documents use the existing memory telescope. -/
public inductive Op : List ObjTy → ObjTy → Type where
  | newRef (schema : Oria.Nbt.Schema) : Oria.Nbt.Any → Op [] (.nbtRef schema)
  | inspectRef {as : List ObjTy} :
      Base as → Path (Scope.Var Unit as .i32) → (numeric : Bool) → Op as .i32
  | inspectValue {as : List ObjTy} {t : Option Oria.Nbt.Tag} :
      Scope.Var Unit as (.nbt t) → Fragment as → (numeric : Bool) → Op as .i32
  | putRef {as : List ObjTy} :
      Base as → Path (Scope.Var Unit as .i32) →
      Write (Scope.Var Unit as .i32) → (append : Bool) → Op as .unit
  | clearRef {as : List ObjTy} :
      Base as → Path (Scope.Var Unit as .i32) → Op as .unit
  | copyRef {as : List ObjTy} :
      Base as → Path (Scope.Var Unit as .i32) →
      Base as → Path (Scope.Var Unit as .i32) → (append : Bool) → Op as .unit
  | exportRef {as : List ObjTy} :
      Base as → Path (Scope.Var Unit as .i32) → Fragment as → Fragment as → Op as .unit
  | literal {t : Oria.Nbt.Tag} : Oria.Nbt.Value t → Op [] (.nbt (some t))
  | integer : Op [.i32] (.nbt (some .int))
  | forget {t : Option Oria.Nbt.Tag} : Op [.nbt t] (.nbt none)
  | number {t : Option Oria.Nbt.Tag} : Op [.nbt t] .i32
  | read {as : List ObjTy} : (mode : ReadMode) → Source as → Op as (.nbt mode.tag)
  | write {as : List ObjTy} {t : Option Oria.Nbt.Tag} :
      Fragment as → Fragment as → Scope.Var Unit as (.nbt t) → Op as .i32

/-- Native NBT primitives return one pointer or a success/payload pair. -/
@[expose] public def Op.width {as : List ObjTy} {a : ObjTy} : Op as a → Nat
  | .newRef .. | .inspectRef .. | .inspectValue .. => 2
  | .putRef .. | .clearRef .. | .copyRef .. | .exportRef .. => 1
  | .literal _ | .integer | .forget => 1
  | .number | .read .. | .write .. => 2

@[expose] public def Op.grade {as : List ObjTy} {a : ObjTy} : Op as a → Grade
  | .newRef .. | .putRef .. | .clearRef .. => writeGrade
  | .inspectRef .. => readGrade
  | .inspectValue .. => .failure
  | .copyRef .. => copyGrade
  | .exportRef _ _ target path =>
      ⟨target.requirements ||| path.requirements,
        Eff.memoryRead ||| Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩
  | .literal _ | .integer | .forget => .pure
  | .number => .failure
  | .read _ source => source.grade
  | .write target path _ =>
      ⟨target.requirements ||| path.requirements,
        Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Native locations used by this operation, for registration checking during collection. -/
public def Op.globals {as : List ObjTy} {a : ObjTy} : Op as a → Array GlobalRef
  | .inspectRef root .. | .putRef root .. | .clearRef root .. | .exportRef root .. => root.globals
  | .copyRef dst _ src _ _ => dst.globals ++ src.globals
  | .read _ (.reference root _) => root.globals
  | _ => #[]

/-- Reify a fragment's holes once as an exact, heterogeneous operand telescope. -/
public def abstractFragment {v : ObjTy → Type} (fragment : Command.Fragment v) :
    (as : List ObjTy) × Fragment as × Args v as :=
  let ⟨as, segments, values⟩ := go fragment.segments
  ⟨as, ⟨segments, fragment.requirements⟩, values⟩
where
  go : List (Command.Segment v) →
      (as : List ObjTy) × List (Command.Segment (Scope.Var Unit as)) × Args v as
    | [] => ⟨[], [], .nil⟩
    | .token t :: rest => let ⟨as, rest, values⟩ := go rest; ⟨as, .token t :: rest, values⟩
    | .space :: rest => let ⟨as, rest, values⟩ := go rest; ⟨as, .space :: rest, values⟩
    | .i32 x :: rest => let ⟨as, rest, values⟩ := go rest; ⟨as, .i32 x :: rest, values⟩
    | .literal x :: rest => let ⟨as, rest, values⟩ := go rest; ⟨as, .literal x :: rest, values⟩
    | .hole (a := a) codec value :: rest =>
        let ⟨as, rest, values⟩ := go rest
        ⟨a :: as, .hole codec .head :: rest.map (Command.Segment.map (fun x => x.weaken a)),
          .cons value values⟩

private theorem abstractSegments_restore {v : ObjTy → Type} (segments : List (Command.Segment v)) :
    let ⟨_, body, values⟩ := abstractFragment.go segments
    body.map (Command.Segment.map (fun x => x.lookup values)) = segments := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
      cases segment <;> simp only [abstractFragment.go]
      all_goals
        generalize eq : abstractFragment.go rest = out at *
        obtain ⟨as, body, values⟩ := out
        dsimp only at ih ⊢
        simp only [List.map_cons]
        congr 1 <;> first
        | (simp only [Command.Segment.map, Scope.Var.lookup_head]; done)
        | simpa only [List.map_map, Function.comp_def, Command.Segment.map_comp,
            Scope.Var.lookup_weaken] using ih

/-- Substituting the captured operands reconstructs the original command fragment exactly. -/
public theorem abstractFragment_restore {v : ObjTy → Type} (fragment : Command.Fragment v) :
    let ⟨_, body, values⟩ := abstractFragment fragment
    body.map (fun x => x.lookup values) = fragment := by
  cases fragment with
  | mk segments requirements =>
      have h := abstractSegments_restore segments
      simp only [abstractFragment, Command.Fragment.map]
      generalize eq : abstractFragment.go segments = out at *
      obtain ⟨as, body, values⟩ := out
      simpa only using
        congrArg (fun segments => (⟨segments, requirements⟩ : Command.Fragment v)) h

end Oria.IR.Nbt
