/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Neighborhood
import StacksCheckRecall

/-!
# Extra permanence for Koszul-regular immersions of locally Noetherian algebraic spaces

The source-facing entry records the corrected algebraic-space regularity criterion
through typed checks of its shared library owner.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.44.10 (authorized correction for tag 09S2): for composable immersions
`i : Z ⟶ Y` and `j : Y ⟶ X`, condition (1) requires Koszul regularity of `j`
on an open subspace of `Y` containing the image of `i`. -/
@[stacks 09S2] #check
  (AlgebraicGeometry.AlgebraicSpace.isKoszulRegularImmersion_tfae_of_comp_and_conormal :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
      (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      List.TFAE
        [ AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i ∧
            ∃ (U : AlgebraicGeometry.AlgebraicSpace.OpenSubspace Y),
              Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map i) ⊆ U.pointsSet ∧
                AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (U.ι ≫ j)
        , AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i ∧
            AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (i ≫ j)
        , AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (i ≫ j) ∧
            AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.IsShortExactLocallySplit
              i j ])

#check
  (AlgebraicGeometry.AlgebraicSpace.isKoszulRegularImmersion_factors_iff_first_and_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
      (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i ∧
          (∃ (U : AlgebraicGeometry.AlgebraicSpace.OpenSubspace Y),
            Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map i) ⊆ U.pointsSet ∧
              AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (U.ι ≫ j)) ↔
        AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i ∧
          AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (i ≫ j))

#check
  (AlgebraicGeometry.AlgebraicSpace.isKoszulRegularImmersion_factors_iff_comp_and_splitConormal :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
      (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [AlgebraicGeometry.AlgebraicSpace.IsImmersion j],
      AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i ∧
          (∃ (U : AlgebraicGeometry.AlgebraicSpace.OpenSubspace Y),
            Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map i) ⊆ U.pointsSet ∧
              AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (U.ι ≫ j)) ↔
        AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (i ≫ j) ∧
          AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.IsShortExactLocallySplit
            i j)
