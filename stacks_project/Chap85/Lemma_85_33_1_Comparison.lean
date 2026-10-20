module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfComparison

/-! # Compatibility checks for simplicial algebraic-space topoi -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped MorphismOfTopoiIn

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.fppfEtaleCommSq :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (fppfEtaleComparison U)⁻¹ ≅
      (spacesFppfComparison X)⁻¹ ⋙ (fppfAugmentation U a)⁻¹)
