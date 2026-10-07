module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.HodgeRegrading

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

/- Example 45.11.1: over `k = F = ℂ`, Hodge-bigraded cohomology regraded by
`(p, q) ↦ 3 * p - q` yields a ℚ-linear realization `G` of Chow motives in
graded ℂ-vector spaces with `G(𝟙(1))` still in degree `-2`; the resulting
classical Weil data can fail range vanishing, since an elliptic curve has
`Module.finrank ℂ` of `G^{-1}(h(E))` equal to `1`. -/
@[stacks 0FHZ]
#check (WeilCohomology.HodgeRegrading.notRangeVanishing :
  ∀ (G₂ : ChowMotive ℂ (fun _ ↦ Correspondence.GradedCategory ℂ) ⥤
      GradedObject (ℤ × ℤ) (ModuleCat ℂ))
    [G₂.Linear ℚ]
    (E : SchemeOverField ℂ) [Variety E] [Smooth E.hom] [Projective E.hom],
    topologicalKrullDim E.left = (1 : WithBot ℕ∞) →
    Module.finrank ℂ
      (((WeilCohomology.HodgeRegrading.realization G₂).obj (ChowMotive.h E)) (-1)) = 1 →
    ¬ ∀ (X : SchemeOverField ℂ) [Variety X] [Smooth X.hom] [Projective X.hom]
        (d : ℕ), topologicalKrullDim X.left = (d : WithBot ℕ∞) →
          ∀ i : ℤ, i < 0 ∨ 2 * (d : ℤ) < i →
            IsZero (((WeilCohomology.HodgeRegrading.realization G₂).obj
              (ChowMotive.h X)) i))

#check WeilCohomology.HodgeRegrading.realization
#check WeilCohomology.HodgeRegrading.tateTwist_degree
#check WeilCohomology.HodgeRegrading.ellipticFinrankNegOne
