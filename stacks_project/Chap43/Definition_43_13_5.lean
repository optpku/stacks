/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.ProperIntersection
import StacksCheckRecall

universe u

/- Definition 43.13.5 (1): closed subvarieties of a nonsingular variety intersect properly when
their intersection satisfies the expected topological Krull-dimension bound. -/
@[stacks 0AZQ] #check (TopologicalSpace.Closeds.IntersectProperly :
  {X : Type u} → [TopologicalSpace X] → TopologicalSpace.Closeds X →
    TopologicalSpace.Closeds X → Prop)

/- Definition 43.13.5 (2): fixed-dimensional algebraic cycles intersect properly when every pair
of components with nonzero coefficient does; the grading is supplied by `dimensionSubgroup`. -/
@[stacks 0AZQ] #check (AlgebraicGeometry.AlgebraicCycle.IntersectProperly :
  {X : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicCycle X ℤ →
    AlgebraicGeometry.AlgebraicCycle X ℤ → Prop)
