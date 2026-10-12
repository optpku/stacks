/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.ProperIntersection

universe u

#check (TopologicalSpace.Closeds.IntersectProperly :
  {X : Type u} → [TopologicalSpace X] → TopologicalSpace.Closeds X →
    TopologicalSpace.Closeds X → Prop)

#check (AlgebraicGeometry.AlgebraicCycle.IntersectProperly :
  {X : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicCycle X ℤ →
    AlgebraicGeometry.AlgebraicCycle X ℤ → Prop)
