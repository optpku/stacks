/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection

@[expose] public section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- On a regular quasi-projective variety, a proper intersection with a rationally trivial
cycle is rationally trivial. -/
theorem intersection_rationallyEquivalent_zero_of_quasiProjective
    {k : Type u} [Field k]
    (X : SchemeOverField k) [QuasiProjectiveVariety X] [Scheme.Regular X.left]
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
