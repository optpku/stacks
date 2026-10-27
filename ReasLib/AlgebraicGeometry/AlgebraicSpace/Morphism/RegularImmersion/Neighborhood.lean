/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Transitivity.Splitting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications

/-!
# Koszul-regular immersions near an image in algebraic spaces

For composable immersions into a locally Noetherian algebraic space, the
neighborhood, composite, and split-conormal formulations of Koszul regularity
are equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

/-- For composable immersions into a locally Noetherian algebraic space, Koszul regularity of the
first immersion and of the second on an open containing its image is equivalent to the two-factor
formulation and to the composite formulation with a locally split conormal sequence. -/
theorem isKoszulRegularImmersion_tfae_of_comp_and_conormal
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    List.TFAE
      [ IsKoszulRegularImmersion i ∧
          ∃ (U : OpenSubspace Y),
            Set.range (Points.map i) ⊆ U.pointsSet ∧
              IsKoszulRegularImmersion (U.ι ≫ j)
      , IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion (i ≫ j)
      , IsKoszulRegularImmersion (i ≫ j) ∧
          IsShortExactLocallySplit i j ] :=
  sorry

/-- Koszul regularity of the first immersion and the second near its image is equivalent to
Koszul regularity of the first immersion and of the composite. -/
theorem isKoszulRegularImmersion_factors_iff_first_and_comp
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    IsKoszulRegularImmersion i ∧
        (∃ (U : OpenSubspace Y),
          Set.range (Points.map i) ⊆ U.pointsSet ∧
            IsKoszulRegularImmersion (U.ι ≫ j)) ↔
      IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion (i ≫ j) :=
  sorry

/-- Koszul regularity of the first immersion and the second near its image is equivalent to
Koszul regularity of the composite together with a locally split conormal sequence. -/
theorem isKoszulRegularImmersion_factors_iff_comp_and_splitConormal
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    IsKoszulRegularImmersion i ∧
        (∃ (U : OpenSubspace Y),
          Set.range (Points.map i) ⊆ U.pointsSet ∧
            IsKoszulRegularImmersion (U.ι ≫ j)) ↔
      IsKoszulRegularImmersion (i ≫ j) ∧
        IsShortExactLocallySplit i j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
