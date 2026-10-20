/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Moving
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFiber
public import ReasLib.AlgebraicGeometry.CycleGroup.Intersection
public import ReasLib.AlgebraicGeometry.ChowGroup

@[expose] public section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- On a regular projective variety over an algebraically closed field, a proper intersection
with a rationally trivial cycle is rationally trivial. -/
theorem intersection_rationallyEquivalent_zero {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [ProjectiveVariety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (β : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α)
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s β))
    (hα : RationalEquivalence.RationallyEquivalent
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α 0) :
    RationalEquivalence.RationallyEquivalent
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (r + s - (X.dimension : ℤ)) (intersection X r s α β hproper) 0 := sorry

end AlgebraicGeometry.CycleGroup
