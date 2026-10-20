module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.PhComparison

/-! # Compatibility checks for simplicial algebraic-space topoi -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped MorphismOfTopoiIn

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.phEtaleAugmentationInverseImageIso :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (U : SimplicialObject (AlgebraicSpace S))
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (phEtaleComparison U)⁻¹ ≅
      (spacesPhComparison X)⁻¹ ⋙ (phAugmentation U a)⁻¹)
