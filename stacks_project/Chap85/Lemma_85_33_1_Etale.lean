/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleAugmentation

/-! # Compatibility checks for simplicial algebraic-space topoi -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped MorphismOfTopoiIn

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.spacesEtaleAugmentation :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    MorphismOfTopoiIn (AlgebraicSpace.spacesEtaleTopology X) (spacesEtaleTotalTopology U))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.spacesEtaleAugmentation_restrict :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : SimplexCategory),
    (spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n ≅
      (AlgebraicSpace.spacesEtaleMorphismOfTopoi (a.app (Opposite.op n)))⁻¹)
