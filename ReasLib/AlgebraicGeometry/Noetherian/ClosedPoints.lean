/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Topology.ClosedPoints
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed Points of Locally Noetherian Schemes

Existence and specialization of closed points for locally Noetherian schemes,
with the corresponding obstruction to a homeomorphism from a space without
closed points.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Every nonempty locally Noetherian scheme has a closed point. -/
@[stacks 02IL "closed points of nonempty locally Noetherian schemes"]
theorem exists_closedPoint [Nonempty X] :
    Set.Nonempty (closedPoints X) := sorry

/-- Every nonempty closed subset of a locally Noetherian scheme contains a point that is closed
in the ambient scheme. -/
@[stacks 02IL "closed points of nonempty closed subsets"]
theorem exists_closedPoint_of_isClosed {Z : Set X} (hZ : IsClosed Z) (hZne : Z.Nonempty) :
    ∃ x : X, x ∈ Z ∧ x ∈ closedPoints X := sorry

/-- Every point of a locally Noetherian scheme specializes to a closed point. -/
@[stacks 02IL "specialization to a closed point"]
theorem specializes_closedPoint (x : X) :
    ∃ y : X, x ⤳ y ∧ y ∈ closedPoints X := sorry

/-- A nonempty space without closed points cannot be homeomorphic to a locally Noetherian
scheme. -/
@[stacks 02HZ "closed-point obstruction to locally Noetherian scheme topology"]
theorem not_homeomorphic_of_closedPoints_eq_empty
    {A : Type v} [TopologicalSpace A] [Nonempty A]
    (hA : closedPoints A = ∅) :
    ¬ Nonempty (A ≃ₜ X) := sorry

end AlgebraicGeometry.Scheme
