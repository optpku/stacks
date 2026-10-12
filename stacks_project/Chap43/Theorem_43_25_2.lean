/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection
import StacksCheckRecall

@[expose] public section

universe u

/- Theorem 43.25.2 -/
@[stacks 0B1V] #check
  (AlgebraicGeometry.CycleGroup.intersection_rationallyEquivalent_zero :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.ProjectiveVariety X]
      [AlgebraicGeometry.Scheme.Regular X.left]
      (r s : ℤ)
      (α : AlgebraicGeometry.CycleGroup X.left
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
      (β : AlgebraicGeometry.CycleGroup X.left
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
      (hproper : AlgebraicGeometry.AlgebraicCycle.IntersectProperly
        (AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α)
        (AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s β))
      (hα : AlgebraicGeometry.RationalEquivalence.RationallyEquivalent
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α 0),
      AlgebraicGeometry.RationalEquivalence.RationallyEquivalent
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + s - (X.dimension : ℤ))
        (AlgebraicGeometry.CycleGroup.intersection X r s α β hproper) 0)
