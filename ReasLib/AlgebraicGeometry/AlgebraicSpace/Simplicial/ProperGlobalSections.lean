module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.GlobalSectionsComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperCohomologicalDescent

/-! # Derived global sections along proper hypercoverings -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- For a proper hypercovering, the canonical total étale augmentation comparison
on bounded-below derived global sections is invertible at every abelian complex. -/
theorem properPlusRGammaInverseImageComparison_app_isIso
    (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((rGammaInverseImageComparison a).app K) := sorry

/-- The comparison `RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` is an isomorphism of
functors on `D⁺(X_étale)` when `a` is a proper hypercovering. -/
theorem properPlusRGammaInverseImageComparison_isIso (ha : IsProperHypercovering a) :
    IsIso (rGammaInverseImageComparison a) := sorry

/-- A proper hypercovering induces an isomorphism on derived global-sections functors. -/
instance properPlusRGammaInverseImageComparison_isIso_of_fact
    [Fact (IsProperHypercovering a)] : IsIso (rGammaInverseImageComparison a) :=
  properPlusRGammaInverseImageComparison_isIso a Fact.out

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
