import Plausible.Arbitrary
import Specimen.ArbitrarySizedSuchThat
import Specimen.DeriveConstrainedProducer
import SpecimenTest.CommonDefinitions.FunctionCallInConclusion
import Plausible.Attr

/-! Tests for `derive_generator` on inductive relations with function calls in constructor conclusions. -/

open Plausible
open DecOpt

set_option guard_msgs.diff true

inductive square_of' : Nat → _ → Prop where
  | sq : forall x, square_of' x (x * x)

inductive square_of'' : Nat → _ → Prop where
  | sq : forall x, square_of'' x (x, x)

inductive square_of''' : Nat → _ → Prop where
  | sq : forall x, square_of''' x (fun (_ : Unit) => x)

-- A `Prod`-shaped (single-constructor) scrutinee keeps its `| _ => MFail` catch-all;
-- Lean's `match.ignoreUnusedAlts` (set by Specimen when elaborating derived code)
-- tolerates the now-redundant catch-all instead of rejecting it. Previously this
-- produced two `Redundant alternative` errors.
#guard_msgs(error, drop info) in
derive_generator (fun n => ∃ (m : Nat), square_of'' m n)

#guard_msgs(drop info) in
derive_generator (fun n => ∃ (m : Nat), square_of' m n)

/--error: exprToConstructorExpr can only handle free variables, constants, and applications. Attempted to convert: Unit → Nat-/
#guard_msgs(error) in
derive_generator (fun n => ∃ (m : Nat), square_of''' m n)

example : Function.Injective (fun a => a * 1) := fun _ _ h => by exact Nat.add_left_cancel h
