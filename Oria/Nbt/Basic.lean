module

public import Init.Data.Float32
public import Init.Data.SInt

namespace Oria.Nbt

public structure Key where
  text : String
  deriving BEq, DecidableEq, Hashable, Repr

/-- Tags of the NBT values exposed by the modern SNBT interface. -/
public inductive Tag where
  | byte | short | int | long | float | double | string
  | byteArray | intArray | longArray | list | compound
  deriving BEq, DecidableEq, Hashable, Repr

mutual
  public inductive Value : Tag → Type where
    | byte : Int8 → Value .byte
    | short : Int16 → Value .short
    | int : Int32 → Value .int
    | long : Int64 → Value .long
    | float : Float32 → Value .float
    | double : Float → Value .double
    | string : String → Value .string
    | byteArray : Array Int8 → Value .byteArray
    | intArray : Array Int32 → Value .intArray
    | longArray : Array Int64 → Value .longArray
    | list : Values → Value .list
    | compound : Fields → Value .compound
    deriving Repr

  /-- Modern SNBT lists allow values with different tags. -/
  public inductive Values where
    | nil : Values
    | cons : {tag : Tag} → Value tag → Values → Values
    deriving Repr

  public inductive Fields where
    | nil : Fields
    | cons : {tag : Tag} → Key → Value tag → Fields → Fields
    deriving Repr
end

public abbrev Any := (tag : Tag) × Value tag

/-- Native values indexed by optional static tag knowledge. -/
@[expose] public def ValueAt : Option Tag → Type
  | none => Any
  | some tag => Value tag

/-- Source type of an immutable runtime NBT value; constructed through object operations. -/
public structure Data (tag : Option Tag := none) where
  private mk ::

namespace Values

@[expose] public def ofArray {tag : Tag} (values : Array (Value tag)) : Values :=
  values.foldr .cons .nil

@[expose] public def ofValues (values : Array Any) : Values :=
  values.foldr (fun ⟨_, value⟩ rest => .cons value rest) .nil

end Values

public inductive PathSegment (i : Type := Int) (p : Type := Empty) where
  | key : Key → PathSegment i p
  | index : i → PathSegment i p
  | all : PathSegment i p
  | matching : p → PathSegment i p
  deriving BEq, DecidableEq, Repr

/-- Change dynamic indices while retaining the native selection structure. -/
@[expose] public def PathSegment.map {i j p : Type} (f : i → j) : PathSegment i p → PathSegment j p
  | .key k => .key k
  | .index ix => .index (f ix)
  | .all => .all
  | .matching pattern => .matching pattern

@[simp] public theorem PathSegment.map_id {i p : Type} (s : PathSegment i p) :
    s.map id = s := by cases s <;> rfl

@[simp] public theorem PathSegment.map_comp {i j k p : Type} (f : i → j) (g : j → k)
    (s : PathSegment i p) : (s.map f).map g = s.map (g ∘ f) := by cases s <;> rfl

/-- A native NBT selection, evaluated segment by segment over all current matches.
For example, `tasks[].n` selects the `n` field of every task that has one. Reading
`tasks` selects the list itself as one value; reading `tasks[]` selects its elements.
The consuming command determines how zero or multiple matches are handled. -/
public structure Path (i : Type := Int) (p : Type := Empty) where
  head : PathSegment i p
  tail : List (PathSegment i p)
  deriving BEq, DecidableEq, Repr

namespace Path

variable {i j p : Type}

@[expose] public def key (key : String) : Path i p := ⟨.key ⟨key⟩, []⟩

@[expose] public def child (path : Path i p) (segment : PathSegment i p) : Path i p :=
  { path with tail := path.tail ++ [segment] }

/-- Read this field from each selected compound; missing fields contribute no match.
Native writes may create missing fields. -/
@[expose] public def field (path : Path i p) (key : String) : Path i p :=
  path.child (.key ⟨key⟩)

@[expose] public def «at» (path : Path i p) (index : i) : Path i p :=
  path.child (.index index)

/-- Select all elements with `[]`; subsequent segments apply to each selected element. -/
@[expose] public def all (path : Path i p) : Path i p := path.child .all

/-- Select list elements matching a compound pattern; suffixes visit each match. -/
@[expose] public def matching (path : Path i p) (pattern : p) : Path i p :=
  path.child (.matching pattern)

/-- Change only index values; key spelling and path structure remain unchanged. -/
@[expose] public def map (f : i → j) (path : Path i p) : Path j p :=
  ⟨path.head.map f, path.tail.map (·.map f)⟩

@[simp] public theorem map_id (path : Path i p) : path.map id = path := by
  cases path
  simp [map]

public theorem map_comp {k : Type} (f : i → j) (g : j → k) (path : Path i p) :
    (path.map f).map g = path.map (g ∘ f) := by
  simp only [map, List.map_map, Function.comp_def, PathSegment.map_comp]

end Path
end Oria.Nbt
