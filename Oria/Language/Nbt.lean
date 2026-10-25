module

public import Oria.Language.Builder
import all Oria.Language.Builder

namespace Oria.Nbt

open Oria.IR

/-- Materialize a host NBT value without converting it through a numeric register. -/
public def literal {t : Tag} (value : Value t) : Prog .pure (Data (some t)) :=
  perform (.memory (.nbt (.literal value)) .nil)

public def ofI32 (value : Val Int32) : Prog .pure (Data (some .int)) :=
  perform (.memory (.nbt .integer) (.cons (reveal value) .nil))

/-- Forget static tag knowledge while sharing the same immutable value. -/
public def forget {t : Option Tag} {r : Region} (value : Val (Data t) r) : Prog .pure Data r :=
  perform (.memory (.nbt (.forget (t := t))) (.cons (reveal value) .nil))

/-- Native scaled numeric read at scale 1. Non-numeric values fail; fractions are floored. -/
public def toI32 {t : Option Tag} {r : Region} (value : Val (Data t) r) : Prog .failure Int32 :=
  perform (.memory (.nbt (.number (t := t))) (.cons (reveal value) .nil))

/-- Use Minecraft's native function-macro serialization. Strings expand as raw text;
numeric formatting follows the server, while collections and compounds expand as SNBT.
Use native value copying when the tag and exact numeric contents must be preserved. -/
@[expose] public def native {t : Option Tag} {r : Region} (value : Val (Data t) r) : Command.Fragment EncodedVal :=
  .hole (.nativeNbt (t := t)) (value : EncodedVal (.nbt t))

private def externalGrade (target : Command.Fragment EncodedVal)
    (path : Option (Command.Fragment EncodedVal)) : Grade :=
  ⟨target.requirements ||| (path.map (·.requirements)).getD Req.none,
    Eff.world ||| Eff.scoreboardRead ||| Eff.random ||| Eff.failure⟩

/-- Library seam for native world selections; operands are abstracted once before Tree. -/
private def readExternal (mode : IR.Nbt.ReadMode) (target : Command.Fragment EncodedVal)
    (path : Option (Command.Fragment EncodedVal)) :
    Prog (externalGrade target path) (Data mode.tag) :=
  match IR.Nbt.abstractFragment (target.append (path.getD .empty)) with
  | ⟨_, fragment, values⟩ =>
      let target' := { fragment with
        segments := fragment.segments.take target.segments.length
        requirements := target.requirements }
      let path' := path.map fun p => { fragment with
        segments := fragment.segments.drop target.segments.length
        requirements := p.requirements }
      have h : (IR.Nbt.Op.read mode (.external target' path')).grade = externalGrade target path := by
        cases path <;> rfl
      h ▸ perform (.memory (.nbt (.read mode (.external target' path')))
        (values.map revealEncoded))

/-- Query an immutable value. The suffix is command syntax including a leading dot for fields. -/
private def readValue {t : Option Tag} {r : Region} (mode : IR.Nbt.ReadMode) (value : Val (Data t) r)
    (path : Option (Command.Fragment EncodedVal)) :
    Prog ⟨(path.map (·.requirements)).getD Req.none, Eff.failure⟩ (Data mode.tag) :=
  match IR.Nbt.abstractFragment (path.getD .empty) with
  | ⟨_, fragment, values⟩ =>
      let path' := path.map fun p =>
        { fragment.map (fun x => x.weaken (.nbt t)) with requirements := p.requirements }
      have h : (IR.Nbt.Op.read mode (.value (t := t) .head path')).grade =
          ⟨(path.map (·.requirements)).getD Req.none, Eff.failure⟩ := by
        cases path <;> rfl
      h ▸ perform (.memory (.nbt (.read mode (.value (t := t) .head path')))
        (.cons (reveal value) (values.map revealEncoded)))

/-- Copy a runtime NBT value to a world location using native `set from`. -/
private def writeExternal {t : Option Tag} {r : Region} (target path : Command.Fragment EncodedVal)
    (value : Val (Data t) r) :
    Prog (externalGrade target (some path)) Int32 :=
  match IR.Nbt.abstractFragment (target.append path) with
  | ⟨_, fragment, values⟩ =>
      let fragment := fragment.map (fun x => x.weaken (.nbt t))
      let target' := { fragment with
        segments := fragment.segments.take target.segments.length
        requirements := target.requirements }
      let path' := { fragment with
        segments := fragment.segments.drop target.segments.length
        requirements := path.requirements }
      have h : (IR.Nbt.Op.write (t := t) target' path' .head).grade =
          externalGrade target (some path) := by
        simp [IR.Nbt.Op.grade, externalGrade, target', path']
      h ▸ perform (.memory (.nbt (.write (t := t) target' path' .head))
        (.cons (reveal value) (values.map revealEncoded)))

end Oria.Nbt
