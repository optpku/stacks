/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.TwoStep

@[expose] public section

/-!
# Successive Upper Truncations and Filtration Steps

@stack 06XX

This leaf specializes the general truncation-transition API to adjacent upper truncations and
relates it to the canonical truncation filtration.  It is independent of any derived-category
representative or spectral-sequence application.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The adjacent upper-truncation cutoffs are canonically ordered. -/
@[stacks 06XX]
theorem truncLEStep_index_le (j : ℤ) : j - 1 ≤ j := sorry

/-- The canonical map from the upper truncation at j - 1 to the upper truncation at j. -/
@[stacks 06XX]
def truncLEStep (K : CochainComplex 𝒜 ℤ) (j : ℤ) :
    K.truncLE (j - 1) ⟶ K.truncLE j :=
  truncLEMapOfLE K (truncLEStep_index_le j)

/-- The successive upper-truncation map composes with the later inclusion to the earlier
truncation inclusion. -/
@[stacks 06XX]
theorem truncLEStep_comp_ιTruncLE (K : CochainComplex 𝒜 ℤ) (j : ℤ) :
    truncLEStep K j ≫ K.ιTruncLE j = K.ιTruncLE (j - 1) := sorry

end CochainComplex

namespace CategoryTheory.CochainComplex.TruncationFiltration

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace Step

/-- The two filtration indices adjacent to `gr^{-j}` are ordered in the canonical direction. -/
@[stacks 06XX]
theorem indexLE (j : ℤ) : -j ≤ 1 - j := sorry

/-- The stage indexed by `-j` is identified with the upper truncation `K.truncLE j`. -/
@[stacks 06XX]
noncomputable def iso
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    (K.truncationFiltration).stage (-j) ≅ K.truncLE j :=
  stageIso K (-j) ≪≫
    eqToIso (congrArg K.truncLE (by omega : -(-j) = j))

/-- The stage immediately preceding `-j` is identified with `K.truncLE (j - 1)`. -/
@[stacks 06XX]
noncomputable def prevIso
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    (K.truncationFiltration).stage (1 - j) ≅ K.truncLE (j - 1) :=
  stageIso K (1 - j) ≪≫
    eqToIso (congrArg K.truncLE (by omega : -(1 - j) = j - 1))

/-- The comparison of adjacent filtration stages agrees with the canonical upper-truncation
step after the two reindexing identifications. -/
@[stacks 06XX]
theorem comparison_hom
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    (K.truncationFiltration).stageComparison (indexLE j) ≫ (iso K j).hom =
      (prevIso K j).hom ≫ _root_.CochainComplex.truncLEStep K j := sorry

/-- The stage `-j + 1` (the successor index used by graded pieces) is identified with the upper
truncation `K.truncLE (j - 1)`. -/
@[stacks 06XX]
noncomputable def succIso
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    (K.truncationFiltration).stage (-j + 1) ≅ K.truncLE (j - 1) :=
  stageIso K (-j + 1) ≪≫
    eqToIso (congrArg K.truncLE (by omega : -(-j + 1) = j - 1))

/-- The successive stage comparison defining `gr^{-j}` agrees with the canonical
upper-truncation step after the reindexing identifications. -/
@[stacks 06XX]
theorem succComparison_hom
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    (K.truncationFiltration).stageComparison (lt_add_one (-j)).le ≫ (iso K j).hom =
      (succIso K j).hom ≫ _root_.CochainComplex.truncLEStep K j := sorry

/-- The `(-j)`-th graded piece of the truncation filtration is isomorphic to the cokernel of
the canonical adjacent upper-truncation step: the degreewise graded piece is first compared with
the categorical cokernel of the successive stage comparison, and that cokernel is then
transported along the stage identifications `succIso` and `iso`. -/
@[stacks 06XX]
noncomputable def gradedPieceIsoCokernel
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    (K.truncationFiltration).gradedPiece (-j) ≅
      cokernel (_root_.CochainComplex.truncLEStep K j) :=
  HomologicalComplex.Filtered.TwoStep.GradedPiece.cokernelIso (K.truncationFiltration) (-j) ≪≫
    cokernel.mapIso _ _ (succIso K j) (iso K j) (succComparison_hom K j)

/-- The forward map of `gradedPieceIsoCokernel` is induced on cokernels by the stage
identifications: precomposed with the cokernel projection of the stage comparison it is the
identification `iso` followed by the cokernel projection of the truncation step. -/
@[stacks 06XX]
theorem π_gradedPieceIsoCokernel_hom
    (K : _root_.CochainComplex 𝒜 ℤ) (j : ℤ) :
    cokernel.π ((K.truncationFiltration).stageComparison (lt_add_one (-j)).le) ≫
        (HomologicalComplex.Filtered.TwoStep.GradedPiece.cokernelIso
          (K.truncationFiltration) (-j)).inv ≫ (gradedPieceIsoCokernel K j).hom =
      (iso K j).hom ≫ cokernel.π (_root_.CochainComplex.truncLEStep K j) := sorry

end Step

end CategoryTheory.CochainComplex.TruncationFiltration
