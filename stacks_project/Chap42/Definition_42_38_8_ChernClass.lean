module

public import stacks_project.Chap42.Lemma_42_38_7_ChernClass

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

variable {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
variable [IsDimensionFunction δ] (p : X ⟶ S) [LocallyOfFiniteType p]
variable (E : X.Modules) (r : ℕ)
variable [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]

/-- The total Chern class of a rank-`r` finite locally free module, assembled in
the Chow-cohomology ring from its homogeneous Chern classes of degrees `0` through `r`. -/
noncomputable def total : ChowCohomology.ring δ p :=
  ∑ i : Fin (r + 1),
    DirectSum.of (ChowCohomology.degree δ p) (i : ℤ) (component δ p E r i)

/-- The total Chern class is the finite direct-sum inclusion of its homogeneous
components in degrees `0` through `r`. -/
theorem total_def :
    total δ p E r =
      ∑ i : Fin (r + 1),
        DirectSum.of (ChowCohomology.degree δ p) (i : ℤ) (component δ p E r i) := sorry

/-- The degree-`i` component of the total Chern class is the `i`th Chern class. -/
theorem total_component (i : Fin (r + 1)) :
    total δ p E r (i : ℤ) = component δ p E r i := sorry

end AlgebraicGeometry.ChernClass
