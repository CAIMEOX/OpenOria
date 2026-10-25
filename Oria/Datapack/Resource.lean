module

public import Oria.Datapack.ResourceId
public import Init.Data.Subtype
import Init.Data.List.SplitOn.Lemmas
public import Std.Data.TreeMap.Basic

namespace Oria.Datapack

open Std

@[expose] public def CanonicalComponent (s : String) : Prop :=
  s ≠ "" ∧ s ≠ "." ∧ s ≠ ".."

public instance (s : String) : Decidable (CanonicalComponent s) := by
  unfold CanonicalComponent
  infer_instance

namespace ResourceNamespace
@[expose] public def Valid (s : String) : Prop :=
  CanonicalComponent s ∧ ∀ c ∈ s.toList, ResourceId.NamespaceCharacter c
public instance (s : String) : Decidable (Valid s) := by unfold Valid; infer_instance
end ResourceNamespace

public abbrev ResourceNamespace := {s : String // ResourceNamespace.Valid s}

namespace ResourceNamespace
@[expose] public def ofString (s : String) (h : Valid s := by decide) : ResourceNamespace :=
  ⟨s, h⟩
public def parse (s : String) : Except ResourceId.Error ResourceNamespace :=
  if h : Valid s then .ok ⟨s, h⟩ else .error (.invalidResourceId s)
@[expose] public def render (x : ResourceNamespace) : String := x.val
end ResourceNamespace

namespace ResourcePath
@[expose] public def SegmentValid (s : String) : Prop :=
  CanonicalComponent s ∧ ∀ c ∈ s.toList, ResourceId.NamespaceCharacter c
public instance (s : String) : Decidable (SegmentValid s) := by unfold SegmentValid; infer_instance
@[expose] public def Valid (s : String) : Prop :=
  s ≠ "" ∧
    (∀ segment ∈ s.splitOn "/", SegmentValid segment) ∧
      ∀ c ∈ s.toList, ResourceId.PathCharacter c
public instance (s : String) : Decidable (Valid s) := by unfold Valid; infer_instance
end ResourcePath

public abbrev ResourcePath := {s : String // ResourcePath.Valid s}

namespace ResourcePath
@[expose] public def ofString (s : String) (h : Valid s := by native_decide) : ResourcePath :=
  ⟨s, h⟩
public def parse (s : String) : Except ResourceId.Error ResourcePath :=
  if h : Valid s then .ok ⟨s, h⟩ else .error (.invalidResourceId s)
@[expose] public def render (p : ResourcePath) : String := p.val
@[expose] public def segments (p : ResourcePath) : List String := p.val.splitOn "/"
@[expose] public def Internal (p : ResourcePath) : Prop := p.segments.head? = some "__oria"
public instance (p : ResourcePath) : Decidable (Internal p) := by unfold Internal; infer_instance

-- Subtype inherits comparison and equality; TreeMap also requires these comparison laws.
public instance : TransOrd ResourcePath where
  eq_swap := OrientedOrd.eq_swap (α := String)
  isLE_trans := TransOrd.isLE_trans (α := String)

public instance : LawfulEqOrd ResourcePath where
  eq_of_compare h := Subtype.ext (LawfulEqOrd.eq_of_compare (α := String) h)
end ResourcePath

public abbrev PublicFunctionPath := {p : ResourcePath // ¬ResourcePath.Internal p}

namespace PublicFunctionPath
@[expose] public def ofString
    (s : String) (h : ResourcePath.Valid s := by native_decide)
    (userSpace : ¬ResourcePath.Internal (ResourcePath.ofString s h) := by native_decide) :
    PublicFunctionPath :=
  ⟨ResourcePath.ofString s h, userSpace⟩
public def parse (s : String) : Except ResourceId.Error PublicFunctionPath := do
  let p ← ResourcePath.parse s
  if h : ¬ResourcePath.Internal p then
    pure ⟨p, h⟩
  else
    throw (.invalidResourceId s)
@[expose] public def render (p : PublicFunctionPath) : String := p.val.render

public instance : TransOrd PublicFunctionPath where
  eq_swap := OrientedOrd.eq_swap (α := ResourcePath)
  isLE_trans := TransOrd.isLE_trans (α := ResourcePath)

public instance : LawfulEqOrd PublicFunctionPath where
  eq_of_compare h := Subtype.ext (LawfulEqOrd.eq_of_compare (α := ResourcePath) h)
end PublicFunctionPath

public structure FunctionId where
  private mk ::
  resourceNamespace : ResourceNamespace
  path : ResourcePath

namespace FunctionId
@[expose] public def ofParts (ns : ResourceNamespace) (p : ResourcePath) : FunctionId :=
  private_decl% ⟨ns, p⟩
@[expose] public def render (id : FunctionId) : String :=
  id.resourceNamespace.render ++ ":" ++ id.path.render
private theorem namespace_no_colon (ns : ResourceNamespace) : ':' ∉ ns.render.toList := by
  intro h
  have valid := ns.property.2 ':' h
  simp [ResourceId.NamespaceCharacter] at valid
private theorem path_no_colon (p : ResourcePath) : ':' ∉ p.render.toList := by
  intro h
  have valid := p.property.2.2 ':' h
  simp [ResourceId.PathCharacter, ResourceId.NamespaceCharacter] at valid
private theorem split_render (id : FunctionId) :
    id.render.toList.splitOn ':' = [id.resourceNamespace.render.toList, id.path.render.toList] := by
  simpa [render] using
    List.splitOn_intercalate
      (ls := [id.resourceNamespace.render.toList, id.path.render.toList]) ':'
      (by simp [namespace_no_colon, path_no_colon]) (by simp)
public theorem render_injective : Function.Injective render :=
  private_decl% (by
    rintro ⟨xns, xp⟩ ⟨yns, yp⟩ h
    have split := congrArg (fun s : String => s.toList.splitOn ':') h
    rw [split_render ⟨xns, xp⟩, split_render ⟨yns, yp⟩] at split
    simp at split
    have nsEqual : xns = yns := Subtype.ext (String.toList_injective split.1)
    have pathEqual : xp = yp := Subtype.ext (String.toList_injective split.2)
    subst yns
    subst yp
    rfl)
end FunctionId

attribute [string_literal ResourceNamespace.ofString] ResourceNamespace
attribute [string_literal ResourcePath.ofString] ResourcePath
attribute [string_literal PublicFunctionPath.ofString] PublicFunctionPath

end Oria.Datapack
