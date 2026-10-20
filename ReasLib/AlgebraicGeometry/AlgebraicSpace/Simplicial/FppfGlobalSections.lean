module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.GlobalSectionsComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfCohomologicalDescent

/-! # Derived global sections along fppf hypercoverings -/

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

/-- For an fppf hypercovering, the canonical total étale augmentation comparison
on bounded-below derived global sections is invertible at every abelian complex. -/
theorem rGammaInverseImageComparison_app_isIso (ha : IsFppfHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((rGammaInverseImageComparison a).app K) :=
  sorry

/-- The comparison `RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` is an isomorphism of functors
on `D⁺(X_étale)`. -/
theorem rGammaInverseImageComparison_isIso (ha : IsFppfHypercovering a) :
    IsIso (rGammaInverseImageComparison a) :=
  (NatTrans.isIso_iff_isIso_app (rGammaInverseImageComparison a)).2
    (rGammaInverseImageComparison_app_isIso a ha)

/-- An fppf hypercovering induces an isomorphism on derived global-sections functors. -/
instance rGammaInverseImageComparison_isIso_of_fact [Fact (IsFppfHypercovering a)] :
    IsIso (rGammaInverseImageComparison a) :=
  rGammaInverseImageComparison_isIso a Fact.out

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
