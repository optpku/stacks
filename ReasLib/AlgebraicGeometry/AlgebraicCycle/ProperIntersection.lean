/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import ReasLib.Topology.KrullDimension.ProperIntersection

/-!
# Proper intersections of algebraic cycles

Proper intersection for algebraic cycles requires proper intersection of the closures of every
pair of points carrying nonzero coefficients.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}}

/-- Two algebraic cycles intersect properly when the closures of every pair of points carrying
nonzero coefficients intersect properly. -/
def IntersectProperly (α β : AlgebraicCycle X ℤ) : Prop :=
  ∀ x y, α x ≠ 0 → β y ≠ 0 →
    TopologicalSpace.Closeds.IntersectProperly
      (TopologicalSpace.Closeds.closure {x}) (TopologicalSpace.Closeds.closure {y})

/-- Proper intersection of algebraic cycles is characterized componentwise by their nonzero
coefficients. -/
theorem intersectProperly_iff (α β : AlgebraicCycle X ℤ) :
    IntersectProperly α β ↔
      ∀ x y, α x ≠ 0 → β y ≠ 0 →
        TopologicalSpace.Closeds.IntersectProperly
          (TopologicalSpace.Closeds.closure {x}) (TopologicalSpace.Closeds.closure {y}) := sorry

/-- Proper intersection of algebraic cycles is symmetric. -/
theorem intersectProperly_comm (α β : AlgebraicCycle X ℤ) :
    IntersectProperly α β ↔ IntersectProperly β α := sorry

/-- The zero cycle intersects every algebraic cycle properly. -/
theorem zero_intersectProperly (β : AlgebraicCycle X ℤ) :
    IntersectProperly 0 β := sorry

/-- Every algebraic cycle intersects the zero cycle properly. -/
theorem intersectProperly_zero (α : AlgebraicCycle X ℤ) :
    IntersectProperly α 0 := sorry

end AlgebraicGeometry.AlgebraicCycle
