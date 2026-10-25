module

public import Oria.Datapack.ResourceId
public import Init.Data.Float32
public import Init.Data.OfScientific
public import Oria.Effect.Labels

namespace Oria.NumberProvider

public inductive Domain where
  | int
  | float
  deriving BEq, DecidableEq, Hashable, Repr

public structure Ref (domain : Domain) where
  id : Oria.ResourceId
  deriving BEq, DecidableEq, Repr

namespace Ref

public def named {domain : Domain} (id : Oria.ResourceId) : Ref domain :=
  ⟨id⟩

end Ref

private inductive Unary : Domain → Domain → Type where
  | abs : {domain : Domain} → Unary domain domain
  | negate : {domain : Domain} → Unary domain domain
  | fromInt : Unary .int .float
  | fromFloat : Unary .float .int
  | ceil : Unary .float .float
  | cos : Unary .float .float
  | floor : Unary .float .float
  | round : Unary .float .float
  | sin : Unary .float .float
  | sqrt : Unary .float .float
  | truncate : Unary .float .float

private inductive Binary : Domain → Type where
  | sub : {domain : Domain} → Binary domain
  | div : {domain : Domain} → Binary domain
  | mod : {domain : Domain} → Binary domain
  | pow : {domain : Domain} → Binary domain
  | floorDiv : Binary .int
  | floorMod : Binary .int

private inductive Aggregate : Domain → Type where
  | add : {domain : Domain} → Aggregate domain
  | mul : {domain : Domain} → Aggregate domain
  | minimum : {domain : Domain} → Aggregate domain
  | maximum : {domain : Domain} → Aggregate domain
  | average : {domain : Domain} → Aggregate domain
  | length : Aggregate .float

/-
Lean rejects `List (Term v domain)` as an indexed nested occurrence. This private nonempty sequence
is the smallest representation that both satisfies strict positivity and enforces DP121's
nonempty `inputs` invariant.
-/
mutual
  private inductive Term (v : Type) : Domain → Type where
    | input : v → Term v .int
    | intConstant : Int → Term v .int
    | floatConstant : Float32 → Term v .float
    | reference : {domain : Domain} → Ref domain → Term v domain
    | unary : {input output : Domain} → Unary input output → Term v input → Term v output
    | binary : {domain : Domain} → Binary domain → Term v domain → Term v domain → Term v domain
    | aggregate : {domain : Domain} → Aggregate domain → Terms v domain → Term v domain
    | uniform : {domain : Domain} → Term v domain → Term v domain → Term v domain
    | binomial : Term v .int → Term v .float → Term v .int

  private inductive Terms (v : Type) : Domain → Type where
    | one : {domain : Domain} → Term v domain → Terms v domain
    | cons : {domain : Domain} → Term v domain → Terms v domain → Terms v domain
end

variable {v : Type}

private def Term.negated {domain : Domain} : Term v domain → Term v domain
  | .intConstant 2_147_483_648 => .intConstant (-2_147_483_648)
  | term => .unary .negate term

public structure Number (domain : Domain) (v : Type := Empty) where
  private mk ::
  private term : Term v domain
  private needs : ReqRow

private inductive RangeTerm (domain : Domain) (v : Type) where
  | exact : Term v domain → RangeTerm domain v
  | bounds : Option (Term v domain) → Option (Term v domain) → RangeTerm domain v

public structure NumberRange (domain : Domain) (v : Type := Empty) where
  private mk ::
  private term : RangeTerm domain v

public abbrev I32 (v : Type := Empty) := Number .int v
public abbrev F32 (v : Type := Empty) := Number .float v

namespace Number

/-- Insert an explicit integer input. The carrier is chosen by the consumer; closed
resource expressions use Empty, and command expressions use object I32 values. -/
public def input (value : v) : Number .int v :=
  ⟨.input value, Req.none⟩

/-- Context dependencies retained during typed provider construction. Resource bodies are
external to this expression; their requirements remain conservative. -/
public def requirements {domain : Domain} (number : Number domain v) : ReqRow := number.needs

public def intConstant (value : Int) : Number .int v :=
  ⟨.intConstant value, Req.none⟩

public def floatConstant (value : Float32) : Number .float v :=
  ⟨.floatConstant value, Req.none⟩

public def reference {domain : Domain} (ref : Ref domain) : Number domain v :=
  ⟨.reference ref, Req.all⟩

private def terms {domain : Domain} (head : Number domain v) : List (Number domain v) → Terms v domain
  | [] => .one head.term
  | number :: rest => .cons head.term (terms number rest)

private def aggregate
    {domain : Domain}
    (operator : Aggregate domain)
    (head : Number domain v)
    (tail : List (Number domain v)) : Number domain v :=
  ⟨.aggregate operator (terms head tail), tail.foldl (fun r n => r ||| n.needs) head.needs⟩

public def add {domain : Domain} (head : Number domain v) (tail : List (Number domain v) := []) : Number domain v :=
  aggregate .add head tail

public def mul {domain : Domain} (head : Number domain v) (tail : List (Number domain v) := []) : Number domain v :=
  aggregate .mul head tail

public def minimum
    {domain : Domain} (head : Number domain v) (tail : List (Number domain v) := []) : Number domain v :=
  aggregate .minimum head tail

public def maximum
    {domain : Domain} (head : Number domain v) (tail : List (Number domain v) := []) : Number domain v :=
  aggregate .maximum head tail

public def average
    {domain : Domain} (head : Number domain v) (tail : List (Number domain v) := []) : Number domain v :=
  aggregate .average head tail

public def length (head : Number .float v) (tail : List (Number .float v) := []) : Number .float v :=
  aggregate .length head tail

private def unary {input output : Domain} (operator : Unary input output) (number : Number input v) :
    Number output v :=
  ⟨.unary operator number.term, number.needs⟩

public def abs {domain : Domain} (number : Number domain v) : Number domain v :=
  unary .abs number

public def negate {domain : Domain} (number : Number domain v) : Number domain v :=
  ⟨number.term.negated, number.needs⟩

public def fromInt (number : Number .int v) : Number .float v :=
  unary .fromInt number

public def fromFloat (number : Number .float v) : Number .int v :=
  unary .fromFloat number

public def ceil (number : Number .float v) : Number .float v :=
  unary .ceil number

public def cos (number : Number .float v) : Number .float v :=
  unary .cos number

public def floor (number : Number .float v) : Number .float v :=
  unary .floor number

public def round (number : Number .float v) : Number .float v :=
  unary .round number

public def sin (number : Number .float v) : Number .float v :=
  unary .sin number

public def sqrt (number : Number .float v) : Number .float v :=
  unary .sqrt number

public def truncate (number : Number .float v) : Number .float v :=
  unary .truncate number

private def binary
    {domain : Domain}
    (operator : Binary domain)
    (left right : Number domain v) : Number domain v :=
  ⟨.binary operator left.term right.term, left.needs ||| right.needs⟩

public def sub {domain : Domain} (left right : Number domain v) : Number domain v :=
  binary .sub left right

public def div {domain : Domain} (left right : Number domain v) : Number domain v :=
  binary .div left right

public def mod {domain : Domain} (left right : Number domain v) : Number domain v :=
  binary .mod left right

public def pow {domain : Domain} (base exponent : Number domain v) : Number domain v :=
  binary .pow base exponent

public def floorDiv (left right : Number .int v) : Number .int v :=
  binary .floorDiv left right

public def floorMod (left right : Number .int v) : Number .int v :=
  binary .floorMod left right

public def uniform {domain : Domain} (minimum maximum : Number domain v) : Number domain v :=
  ⟨.uniform minimum.term maximum.term, minimum.needs ||| maximum.needs⟩

public def binomial (n : Number .int v) (p : Number .float v) : Number .int v :=
  ⟨.binomial n.term p.term, n.needs ||| p.needs⟩

@[simp] public theorem input_requirements (x : v) :
    (input x).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem intConstant_requirements (n : Int) :
    (intConstant (v := v) n).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem floatConstant_requirements (n : Float32) :
    (floatConstant (v := v) n).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem reference_requirements {d : Domain} (ref : Ref d) :
    (reference (v := v) ref).requirements = Req.all := private_decl% (by rfl)

@[simp] public theorem sub_requirements {d : Domain} (x y : Number d v) :
    (sub x y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem addPair_requirements {d : Domain} (x y : Number d v) :
    (add x [y]).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem mulPair_requirements {d : Domain} (x y : Number d v) :
    (mul x [y]).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem div_requirements {d : Domain} (x y : Number d v) :
    (div x y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem floorDiv_requirements (x y : Number .int v) :
    (floorDiv x y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem floorMod_requirements (x y : Number .int v) :
    (floorMod x y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem fromInt_requirements (x : Number .int v) :
    (fromInt x).requirements = x.requirements := private_decl% (by rfl)

@[simp] public theorem sqrt_requirements (x : Number .float v) :
    (sqrt x).requirements = x.requirements := private_decl% (by rfl)

@[simp] public theorem negate_requirements {d : Domain} (x : Number d v) :
    (negate x).requirements = x.requirements := private_decl% (by rfl)

@[simp] public theorem uniform_requirements {d : Domain} (x y : Number d v) :
    (uniform x y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

end Number

namespace NumberRange

public def exact {domain : Domain} (number : Number domain v) : NumberRange domain v :=
  ⟨.exact number.term⟩

public def between {domain : Domain} (minimum maximum : Number domain v) : NumberRange domain v :=
  ⟨.bounds (some minimum.term) (some maximum.term)⟩

public def atLeast {domain : Domain} (minimum : Number domain v) : NumberRange domain v :=
  ⟨.bounds (some minimum.term) none⟩

public def atMost {domain : Domain} (maximum : Number domain v) : NumberRange domain v :=
  ⟨.bounds none (some maximum.term)⟩

public def any {domain : Domain} : NumberRange domain v :=
  ⟨.bounds none none⟩

end NumberRange

public instance {domain : Domain} : Coe (Ref domain) (Number domain v) :=
  ⟨Number.reference⟩

public instance {value : Nat} : OfNat (Number .int v) value where
  ofNat := Number.intConstant value

public instance {value : Nat} : OfNat (Number .float v) value where
  ofNat := Number.floatConstant (Float32.ofNat value)

public instance : NatCast (Number .int v) where
  natCast value := Number.intConstant value

public instance : NatCast (Number .float v) where
  natCast value := Number.floatConstant (Float32.ofNat value)

public instance : IntCast (Number .int v) where
  intCast := Number.intConstant

public instance : IntCast (Number .float v) where
  intCast value := Number.floatConstant (Float32.ofInt value)

public instance : Coe Float32 (Number .float v) :=
  ⟨Number.floatConstant⟩

public instance : OfScientific (Number .float v) where
  ofScientific mantissa sign exponent :=
    Number.floatConstant (OfScientific.ofScientific mantissa sign exponent : Float32)

public instance {domain : Domain} : Add (Number domain v) :=
  ⟨fun left right => Number.add left [right]⟩

public instance {domain : Domain} : Sub (Number domain v) :=
  ⟨Number.sub⟩

public instance {domain : Domain} : Mul (Number domain v) :=
  ⟨fun left right => Number.mul left [right]⟩

public instance {domain : Domain} : Div (Number domain v) :=
  ⟨Number.div⟩

public instance {domain : Domain} : Mod (Number domain v) :=
  ⟨Number.mod⟩

public instance {domain : Domain} : Neg (Number domain v) :=
  ⟨Number.negate⟩

public instance {domain : Domain} : Min (Number domain v) :=
  ⟨fun left right => Number.minimum left [right]⟩

public instance {domain : Domain} : Max (Number domain v) :=
  ⟨fun left right => Number.maximum left [right]⟩

public instance {domain : Domain} : HPow (Number domain v) (Number domain v) (Number domain v) :=
  ⟨Number.pow⟩

public instance {domain : Domain} : HPow (Number domain v) Nat (Number domain v) :=
  ⟨fun number exponent =>
    match domain with
    | .int => Number.pow number (Number.intConstant exponent)
    | .float => Number.pow number (Number.floatConstant (Float32.ofNat exponent))⟩

@[simp] public theorem Number.numeral_requirements (n : Nat) :
    (no_index (OfNat.ofNat n) : Number .int v).requirements = Req.none := private_decl% (by rfl)

@[simp] public theorem Number.add_requirements {d : Domain} (x y : Number d v) :
    (x + y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem Number.mul_requirements {d : Domain} (x y : Number d v) :
    (x * y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem Number.subtract_requirements {d : Domain} (x y : Number d v) :
    (x - y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

@[simp] public theorem Number.divide_requirements {d : Domain} (x y : Number d v) :
    (x / y).requirements = x.requirements ||| y.requirements := private_decl% (by rfl)

public structure References where
  ints : List (Ref .int)
  floats : List (Ref .float)
  deriving BEq, DecidableEq, Repr

namespace References

private def empty : References :=
  ⟨[], []⟩

private def merge (left right : References) : References :=
  ⟨left.ints ++ right.ints, left.floats ++ right.floats⟩

private def deduplicate (references : References) : References :=
  ⟨references.ints.eraseDups, references.floats.eraseDups⟩

end References

private def referenceSet : {domain : Domain} → Ref domain → References
  | .int, ref => ⟨[ref], []⟩
  | .float, ref => ⟨[], [ref]⟩

mutual
  private def Term.references {domain : Domain} : Term v domain → References
    | .input _ | .intConstant _ | .floatConstant _ => References.empty
    | .reference ref => referenceSet ref
    | .unary _ number => number.references
    | .binary _ left right | .uniform left right | .binomial left right =>
        left.references.merge right.references
    | .aggregate _ inputs => inputs.references

  private def Terms.references {domain : Domain} : Terms v domain → References
    | .one term => term.references
    | .cons term rest => term.references.merge rest.references
end

namespace Number

public def references {domain : Domain} (number : Number domain v) : References :=
  number.term.references.deduplicate

end Number

private def optionalReferences {domain : Domain} : Option (Term v domain) → References
  | none => References.empty
  | some term => term.references

namespace NumberRange

public def references {domain : Domain} (range : NumberRange domain v) : References :=
  let references :=
    match range.term with
    | .exact term => term.references
    | .bounds minimum maximum =>
        (optionalReferences minimum).merge (optionalReferences maximum)
  references.deduplicate

end NumberRange

end Oria.NumberProvider
