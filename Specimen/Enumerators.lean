import Specimen.LazyList
import Specimen.Utils
import Plausible.Gen

-- The `Enum (α × β)` instance is polymorphic over `{α β}` that only co-occur in
-- its type; keep them at independent universes rather than couple them, so
-- disable the `checkUnivs` lint for this file.
set_option linter.checkUnivs false

open LazyList Plausible

/-- An enumerator is a function from `Nat` to `LazyList α`, where the `Nat`
    serves an upper bound for the enumeration process, i.e. the LazyList returned
    contains all inhabitants of `α` up to the given size. -/
abbrev Enumerator (α : Type u) := Nat → LazyList α

/-- The `Enum` typeclass describes types that have an associated `Enumerator` -/
class Enum (α : Type u) where
  enum : Enumerator α

/-- The `EnumSized` typeclass describes enumerators that have an
    additional `Nat` parameter to bound their recursion depth. -/
class EnumSized (α : Type u) where
  enumSized : Nat → Enumerator α

/-- Sized enumerators of type `α` such that `P : α -> Prop` holds for all enumerated values.
    Note that these enumerators may fail, which is why they have type `ExceptT GenError Enumerator α`. -/
class EnumSizedSuchThat (α : Type) (P : α → Prop) where
  enumSizedST : Nat → ExceptT GenError Enumerator α

/-- Enumerators of type `α` such that `P : α -> Prop` holds for all generated values.
    Note that these enumerators may fail, which is why they have type `ExceptT GenError Enumerator α`. -/
class EnumSuchThat (α : Type) (P : α → Prop) where
  enumST : ExceptT GenError Enumerator α

/-- `pure x` constructs a trivial enumerator which produces a singleton `LazyList` containing `x` -/
def pureEnum (x : α) : Enumerator α :=
  fun _ => pureLazyList x

/-- Monadic-bind for enumerators -/
def bindEnum (enum : Enumerator α) (k : α → Enumerator β) : Enumerator β :=
  fun (n : Nat) => do
    let x ← enum n
    (k x) n

/-- `Monad` instance for `Enumerator`s -/
instance : Monad Enumerator where
  pure := pureEnum
  bind := bindEnum

/-- The degenerate enumerator which enumerates nothing (the empty `LazyList`) -/
def failEnum : Enumerator α :=
  fun _ => .lnil

/-- `EnumSizedSuchThat` instance for equality propositions
     where a variable `x` is left-equal to some value `val`.
    (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type} {val : α} : EnumSizedSuchThat α (fun x => x = val) where
  enumSizedST _ := return val

/-- `EnumSizedSuchThat` instance for equality propositions
     where a variable `x` is right-equal to some value `val`.
     (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type} {val : α} : EnumSizedSuchThat α (fun x => val = x) where
  enumSizedST _ := return val

/-- `Alternative` instance for `Enumerator`s.
    Note:
    - `e1 <|> e2` is not fair and is biased towards `e1`, i.e. all elements of `e1` will
      appear in the resultant enumeration before the first element of `e2`.
    - Defining a fair instance of `Alternative` requires defining an interleave operation
      on the resultant lists (see "A Completely Unique Account of Enumeration", ICFP '22),
      however it is unclear how to define an interleave operation on *LazyLists* while
      convincing Lean's termination checker to accept the definition (essentially, the
      difficulty lies in proving that forcing the thunked tail of a `LazyList` doesn't
      increase the size of the overall `LazyList`). -/
instance : Alternative Enumerator where
  failure := failEnum
  orElse e1 e2 := fun n => (e1 n) <|> (e2 () n)

/-- `sizedEnum f` constructs an enumerator that depends on `size` parameter -/
def sizedEnum (f : Nat → Enumerator α) : Enumerator α :=
  fun (n : Nat) => (f n) n

/-- Every `EnumSized` instance gives rise to an `Enum` instance -/
instance [EnumSized α] : Enum α where
  enum := sizedEnum EnumSized.enumSized

/-- Every `EnumSizedSuchThat` instance gives rise to an `EnumSuchThat` instance -/
instance [EnumSizedSuchThat α P] : EnumSuchThat α P where
  enumST := sizedEnum (EnumSizedSuchThat.enumSizedST P)

/-- Produces a `LazyList` containing all `Int`s in-between
    `lo` and `hi` (inclusive) in ascending order -/
def lazyListNatRange (lo : Nat) (hi : Nat) : LazyList Nat :=
  lazySeq .succ lo (.succ (hi - lo))

/-- Enumerates all `Nat`s in-between `lo` and `hi` (inclusive)
    in ascending order -/
def enumNatRange (lo : Nat) (hi : Nat) : Enumerator Nat :=
  fun _ => lazyListNatRange lo hi

/-- `EnumSized` instance for `Nat` -/
instance : EnumSized Nat where
  enumSized (n : Nat) := enumNatRange 0 n

namespace EnumeratorCombinators

/-- `vectorOf k e` creates an enumerator of lists of length `k`,
    where each element in the list comes from the enumerator `e` -/
def vectorOf (k : Nat) (e : Enumerator α) : Enumerator (List α) :=
  List.foldr (fun m m' => do
    let x ← m
    let xs ← m'
    return x::xs) (init := pure []) (List.replicate k e)

/-- Picks one of the enumerators in `es`, returning the `default` enumerator
    if `es` is empty. -/
def oneOfWithDefault (default : Enumerator α) (es : List (Enumerator α)) : Enumerator α :=
  match es with
  | [] => default
  | _ => do
    let idx ← enumNatRange 0 (es.length - 1)
    List.getD es idx default

/-- Picks one of the enumerators in `es`, or the `default` value if `es = []`. -/
def oneOf [Inhabited α] (es : List (Enumerator α)) : Enumerator α :=
  oneOfWithDefault (pure default) es

end EnumeratorCombinators

-- Some simple `Enum` instances

/-- `Enum` instance for `Bool` -/
instance : Enum Bool where
  enum := pureEnum false <|> pureEnum true

/-- `Enum` instance for `Option`s -/
instance [Enum α] : Enum (Option α) where
  enum := EnumeratorCombinators.oneOf [
    pure none,
    some <$> Enum.enum
  ]

/-- `Enum` instance for `Except`s, though we do not enumerate the possible exceptions thrown: typically we
  want to enumerate the "positive instances", so we simply throw `.error default` once.
-/
instance [Inhabited ε] [Enum α] : Enum (Except ε α) where
  enum := EnumeratorCombinators.oneOf [
    pure (.error default),
    .ok <$> Enum.enum
  ]

/-- `Enum` instances for pairs -/
instance [Enum α] [Enum β] : Enum (α × β) where
  enum := fun n => do
    let a ← Enum.enum n
    let b ← Enum.enum n
    pure (a, b)

/-- `Enum` instances for sums -/
instance [Enum α] [Enum β] : Enum (α ⊕ β) where
  enum := fun n =>
    (Enum.enum n >>= pure ∘ Sum.inl) <|> (Enum.enum n >>= pure ∘ Sum.inr)

/-- Produces a `LazyList` containing all `Int`s in-between
    `lo` and `hi` (inclusive) in ascending order -/
def lazyListIntRange (lo : Int) (hi : Int) : LazyList Int :=
  lazySeq (. + 1) lo (Int.toNat (hi - lo + 1))

/-- `Enum` instance for `Int` (enumerates all `int`s between `-size` and `size` inclusive) -/
instance : Enum Int where
  enum := fun size =>
    let n := Int.ofNat size
    lazyListIntRange (-n) n

/-- `EnumSized` instance for lists -/
instance [Enum α] : EnumSized (List α) where
  enumSized (n : Nat) := do
    let x ← enumNatRange 0 n
    EnumeratorCombinators.vectorOf x Enum.enum

/-- Enumerates all printable ASCII characters (codepoint 32 - 95) -/
def enumPrintableASCII (size : Nat) : LazyList Char :=
  lazySeq (fun c => Char.ofNat (c.toNat + 1)) (Char.ofNat 32) (min size 95)

/-- `Enum` instance for ASCII-printable `Char`s -/
instance : Enum Char where
  enum := enumPrintableASCII

/-- `Enum` instance for `String`s containing ASCII-printable characters -/
instance : Enum String where
  enum := String.ofList <$> (Enum.enum : Enumerator (List Char))

/-- `Enum` instance for `Fin n` where `n > 0`
  (enumerates all `Nat`s from 0 to `n - 1` inclusive) -/
instance [NeZero n] : Enum (Fin n) where
  enum := fun _ =>
    (Fin.ofNat n) <$> lazyListNatRange 0 (n - 1)

/-- `Enum` instance for `BitVec w`
    (uses the `Enum` instance for `Fin (2 ^ w)`, since bitvectors
    are represented using `Fin (2 ^ w)` under the hood) -/
instance : Enum (BitVec w) where
  enum := BitVec.ofFin <$> (Enum.enum : Enumerator (Fin (2 ^ w)))


-- Sampling from enumerators

/-- Returns a list of up to `limit` elements produced by the enumerator
    associated with the `Enum` instance for a type,
    using `size` as the size parameter for the enumerator.
    To invoke this function, you will need to specify what type `α` is,
    for example by doing `runEnum (α := Nat) 10`. -/
def runEnum [Enum α] (size : Nat) (limit : Nat := 10) : IO (List α) :=
  return (LazyList.take limit $ Enum.enum size)

/-- Samples from an `ExceptT GenError Enumerator` enumerator that is parameterized by its `size`,
    returning the enumerated list of `Except GenError α` values (containing up to `limit` elements) in the `IO` monad -/
def runSizedEnum (sizedEnum : Nat → ExceptT GenError Enumerator α) (size : Nat) (limit : Nat := 10) : IO (List (Except GenError α)) :=
  return (LazyList.take limit $ (sizedEnum size) size)

/-- Like `runSizedEnum`, but filters out errors and pairs each successful value with the
    accumulated error count seen so far. A nonzero error count means the enumeration was
    incomplete at this size — try a larger size for more results. -/
def runSizedEnumOk (sizedEnum : Nat → ExceptT GenError Enumerator α) (size : Nat) : LazyList (α × Nat) :=
  let raw := (sizedEnum size) size
  let rec go (l : LazyList (Except GenError α)) (errCount : Nat) : LazyList (α × Nat) :=
    match l with
    | .lnil => .lnil
    | .lcons x xs =>
      match x with
      | .ok v => .lcons (v, errCount) (Thunk.mk fun _ => go xs.get errCount)
      | .error _ => go xs.get (errCount + 1)
  go raw 0
