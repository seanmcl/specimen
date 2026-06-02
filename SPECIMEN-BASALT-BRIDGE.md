# Bridging Specimen and Basalt via `BacktrackGen`

This document describes a plan to make [Specimen](https://github.com/strata-org/specimen)-derived generators compatible with [Basalt](https://code.amazon.com/packages/Basalt)'s correctness proof infrastructure.

## 1. Status Quo

### The three frameworks

**Plausible** is a property-based testing library for Lean. Its `Gen` monad is a stack of monad transformers:
```
abbrev Gen (α : Type u) := RandT (ReaderT (ULift Nat) (Except GenError)) α
```
It provides randomness, a size parameter, and exception-based failure. The `plausible` tactic finds `Testable` instances (which bottom out at `Arbitrary` instances) via typeclass synthesis and executes them.

**Specimen** derives generators for values satisfying inductive relations, built on top of Plausible. It emits `Plausible.Gen α` terms that use `throw`/`tryCatch` for backtracking: when a branch can't satisfy constraints, it throws a `GenError`, and the `backtrack` combinator catches it and retries another branch. Key typeclasses:
- `ArbitrarySizedSuchThat α P` — a sized generator (`Nat → Gen α`) for values satisfying `P`
- `ArbitrarySuchThat α P` — the unsized wrapper (via `Gen.sized`)

**Basalt** defines a `Gen` typeclass abstracting the capabilities needed by a generator:
```lean
class Gen (g : Type u → Type v) where
  instInhabited : ∀ α, Inhabited (g α)
  instMonad : Monad g
  instRandomChoice : RandomChoice g
  instCCPO : ∀ α, CCPO (g α)
  instMonoBind : MonoBind g
```
Basalt provides multiple instances: `SetGen.Set` (for soundness/completeness proofs), `SPMF` (for termination/distribution proofs), `SPMF.Cost` (for cost bounds), and `Plausible.Gen` (for execution, via `Basalt/PlausibleGen.lean`). A generator written polymorphically as `[Gen G] → G α` can be proved correct at `SetGen`/`SPMF` and executed at `Plausible.Gen`.

### Current dependency structure

```
Plausible ← Specimen    (Specimen emits Plausible.Gen terms)
Plausible ← Basalt      (PlausibleGen makes Plausible.Gen a Basalt Gen instance)
```

Specimen and Basalt are currently unrelated — Specimen-derived generators cannot be reasoned about using Basalt's correctness classes.

### The problem

Specimen emits generators that target `Plausible.Gen` directly. These generators cannot be instantiated at `SetGen.Set` or `SPMF` for proofs. To prove a Specimen-derived generator is sound, complete, terminating, or cost-bounded, we need it to be polymorphic over Basalt's `Gen` class.

The core challenge is **backtracking**. Specimen's `backtrack` combinator uses Plausible's `throw`/`tryCatch` (exception-based control flow) to retry branches. Basalt has no exception mechanism — its `Gen` class provides only `choose`, `bind`, `pure`, and ⊥ (`default`). We need a way to express backtracking that works across all Basalt interpretations.

## 2. The Change: `BacktrackGen`

We introduce a newtype that wraps `G (Option α)` to represent generators that may fail locally:

```lean
/-- A backtracking generator: G (Option α) where none = local failure, some = success. -/
def BacktrackGen (G : Type → Type) (α : Type) := G (Option α)
```

The `Option` layer is *inside* the generator monad `G`, meaning failure is a **value** that the generator successfully produces (as opposed to ⊥/`default`, which represents divergence). This lets other generators observe and react to failure — enabling retry.

### The `backtrack` combinator

```lean
/-- Weighted backtracking: randomly pick a branch by weight, try it, retry remaining on failure. -/
def backtrack [Gen G] (gs : List (Nat × (Unit → BacktrackGen G α))) : BacktrackGen G α :=
  go (sumWeights gs) gs
where
  go (total : Nat) : List (Nat × (Unit → BacktrackGen G α)) → BacktrackGen G α
  | [] => pure none
  | gs => do
    let n ← choose 0 (total - 1) (by omega)
    let (k, g, rest) := pickDrop gs n
    match ← g () with
    | some a => pure (some a)
    | none => go (total - k) rest
```

This has identical operational semantics to Specimen's current `backtrack`: pick a branch randomly by weight, run it, and if it returns `none` (failure), remove it from the pool and retry with adjusted weights.

### Boundary: unwrapping `BacktrackGen` to `Gen`

At the outermost level — where a generator must produce a value for Plausible's testing machinery — we collapse the `Option`:

```lean
def BacktrackGen.run [Gen G] (g : BacktrackGen G α) : G α := do
  match ← g with
  | some a => pure a
  | none => default  -- ⊥ (divergence)

def BacktrackGen.toPlausibleGen (g : BacktrackGen Plausible.Gen α) : Plausible.Gen α := do
  match ← g with
  | some a => pure a
  | none => throw (.genError "backtracking exhausted")
```

### Why a newtype?

Without the newtype, `G (Option α)` is ambiguous — it could be a generator that legitimately produces `Option` values (where `none` is a valid output) or a backtracking generator where `none` signals failure. `BacktrackGen` makes the intent explicit at the type level.

### Composability

Internal backtracking generators compose by staying in `BacktrackGen G`:

```lean
-- A Stmt generator calling an Expr generator — failure propagates naturally
def genStmt [Gen G] (ctx : Ctx) : BacktrackGen G Stmt := do
  let some e ← genExpr ctx τ | pure none   -- observe failure, propagate
  pure (some (Stmt.assign x e))
```

Failure information is only lost at the outermost boundary (`toPlausibleGen`). This avoids the problem where wrapping a sub-generator too early prevents the caller from backtracking through it.

### Interpretations across Basalt instances

| Instance | `BacktrackGen G α` is... | `none` means... | `some a` means... |
|---|---|---|---|
| `SetGen.Set` | `Set (Option α)` | failure is reachable | `a` is reachable |
| `SPMF` | `SPMF (Option α)` | mass on failure | mass on producing `a` |
| `SPMF.Cost` | `SPMF (Option α × Nat)` | failure with cost `n` | producing `a` with cost `n` |
| `Plausible.Gen` | `Plausible.Gen (Option α)` | generation failed | generation succeeded |

### Cost tracking

Basalt's `SPMF.Cost` tracks the number of `choose` calls. In `backtrack`, each retry costs one `choose` (to select the next branch) plus whatever choices that branch made. The cost of backtracking falls out automatically from existing `IsBounded_bind` and `IsBounded_choose` theorems — no new cost infrastructure is needed. You can prove bounds like "producing value `a` costs at most `n + c(a)`" where `n` is the number of branches (worst-case retries) and `c(a)` is the cost of the successful branch.

### New dependency structure

```
Plausible ← Basalt ← Specimen
```

Specimen depends on Basalt for `Gen`, `BacktrackGen`, and `backtrack`. The `plausible` tactic still works: Specimen emits `ArbitrarySizedSuchThat` instances (as it does today) whose body calls `BacktrackGen.toPlausibleGen` to produce the `Plausible.Gen α` that Plausible's machinery expects.

## 3. Example

Consider a simple typing relation:

```lean
inductive Ty | nat | bool
inductive Expr | lit (n : Nat) | isZero (e : Expr)

inductive HasType : Expr → Ty → Prop
  | litNat (n : Nat) : HasType (.lit n) .nat
  | isZero (e : Expr) : HasType e .nat → HasType (.isZero e) .bool
```

### What Specimen emits today

```lean
def genHasType (τ : Ty) : Nat → Plausible.Gen Expr
  | 0 => GeneratorCombinators.backtrack [
      (1, match τ with | .nat => do let n ← Arbitrary.arbitrary; pure (.lit n)
                       | _ => throw Gen.genericFailure)]
  | size + 1 => GeneratorCombinators.backtrack [
      (1, match τ with | .nat => do let n ← Arbitrary.arbitrary; pure (.lit n)
                       | _ => throw Gen.genericFailure),
      (1, match τ with | .bool => do let e ← genHasType .nat size; pure (.isZero e)
                       | _ => throw Gen.genericFailure)]
```

This can be executed but not proved correct.

### What Specimen would emit after the change

```lean
def genHasType [Gen G] (τ : Ty) : Nat → BacktrackGen G Expr
  | 0 => backtrack [
      (1, fun () => match τ with
        | .nat => do let n ← liftGen (genNat : G Nat); pure (some (.lit n))
        | _ => pure none)]
  | size + 1 => backtrack [
      (1, fun () => match τ with
        | .nat => do let n ← liftGen (genNat : G Nat); pure (some (.lit n))
        | _ => pure none),
      (1, fun () => match τ with
        | .bool => do
            let some e ← genHasType .nat size | pure none
            pure (some (.isZero e))
        | _ => pure none)]
where
  liftGen (g : G α) : BacktrackGen G α := do let a ← g; pure (some a)
```

### Proving correctness (at `SetGen.Set`)

```lean
theorem genHasType_sound (τ : Ty) (size : Nat) (e : Expr) :
    some e ∈ SetGen.support (genHasType (G := SetGen.Set) τ size) → HasType e τ := ...

theorem genHasType_complete (τ : Ty) (e : Expr) (h : HasType e τ) :
    ∃ size, some e ∈ SetGen.support (genHasType (G := SetGen.Set) τ size) := ...
```

### Executing via Plausible

```lean
instance : ArbitrarySizedSuchThat Expr (HasType · τ) where
  arbitrarySizedST size := BacktrackGen.toPlausibleGen (genHasType τ size)
```

The `plausible` tactic finds this instance via the existing `ArbitrarySizedSuchThat → ArbitrarySuchThat → Arbitrary` chain and executes it normally.

### The size pattern

The generator takes `size : Nat` as an explicit parameter (structural recursion ensures termination). At the Plausible call site, `Gen.sized` bridges Plausible's reader-based size to this parameter:

```lean
instance : ArbitrarySuchThat Expr (HasType · τ) where
  arbitraryST := Gen.sized (fun n => BacktrackGen.toPlausibleGen (genHasType τ n))
```

## 4. Plan of Work

### Step 1: Define `BacktrackGen` in Basalt

- Define `BacktrackGen G α := G (Option α)` as a newtype
- Implement helper functions: `pure`/`fail`/`bind`/`liftGen` for `BacktrackGen`
- Implement `BacktrackGen.run` and `BacktrackGen.toPlausibleGen`
- Implement the `backtrack` combinator (weighted random selection with retry)
- Implement `frequency` combinator (weighted random selection, no retry — for unconstrained generators)

### Step 2: Prove SetGen support lemmas

- `backtrack_mem_iff`: `some a ∈ support (backtrack gs)` iff `some a ∈ support (gᵢ ())` for some `i`
- `frequency_mem_iff`: analogous for `frequency`
- Basic `liftGen`/`pure`/`bind` support lemmas

### Step 3: Modify Specimen's code emission

- Replace `GeneratorCombinators.backtrack` with Basalt's `backtrack` over `BacktrackGen G`
- Replace `Gen.frequency` / `oneOfWithDefault` with Basalt's `frequency`
- Replace `throw` with `pure none`
- Replace fuel-based recursion with structural recursion on an explicit `size : Nat`
- Emit generators polymorphic over `[Gen G]` instead of targeting `Plausible.Gen`
- Emit `ArbitrarySizedSuchThat` instances that call `BacktrackGen.toPlausibleGen`

### Step 4: Validate the pipeline

- Verify existing Specimen test cases still pass (generators execute correctly via Plausible)
- Write a small proof (e.g., the `HasType` example) demonstrating that a Specimen-derived generator can be proved sound at `SetGen.Set`
- Verify the `plausible` tactic works end-to-end with the new generators
