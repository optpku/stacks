/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

@[expose] public section

open Set Topology

universe u v

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}} {R : Type v} [Zero R]

/-- The geometric support of an algebraic cycle is the union of the closures of the points
where its coefficient is nonzero. -/
def geometricSupport (α : AlgebraicCycle X R) : Set X :=
  ⋃ x ∈ Function.support α, closure {x}

/-- The geometric support is the union of the point closures indexed by coefficient support. -/
theorem geometricSupport_def (α : AlgebraicCycle X R) :
    geometricSupport α = ⋃ x ∈ Function.support α, closure {x} := sorry

/-- A point belongs to the geometric support exactly when it specializes from a point with
nonzero coefficient. -/
theorem mem_geometricSupport (α : AlgebraicCycle X R) (y : X) :
    y ∈ geometricSupport α ↔ ∃ x : X, α x ≠ 0 ∧ y ∈ closure {x} := sorry

/-- The geometric support of an algebraic cycle is closed. -/
theorem isClosed_geometricSupport (α : AlgebraicCycle X R) :
    IsClosed (geometricSupport α) := sorry

end AlgebraicGeometry.AlgebraicCycle
