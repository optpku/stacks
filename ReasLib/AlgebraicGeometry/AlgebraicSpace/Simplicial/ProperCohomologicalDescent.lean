module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperHypercovering

/-! # Étale cohomological descent for proper hypercoverings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- For a proper hypercovering, the derived unit of total étale augmentation is
invertible on every bounded-below complex of abelian étale sheaves. -/
theorem properPlusDerivedUnit_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((EtaleDerived.plusDerivedUnit a).app K) :=
  sorry

/-- The derived unit of total étale augmentation for a proper hypercovering is
an isomorphism of functors on the bounded-below derived category. -/
theorem properPlusDerivedUnit_isIso (ha : IsProperHypercovering a) :
    IsIso (EtaleDerived.plusDerivedUnit a) :=
  (NatTrans.isIso_iff_isIso_app (EtaleDerived.plusDerivedUnit a)).2
    (properPlusDerivedUnit_app_isIso a ha)

end AlgebraicGeometry.AlgebraicSpace.Simplicial
