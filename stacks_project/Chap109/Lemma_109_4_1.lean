module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap109.Lemma_109_4_1_PolarizedCurves
public import stacks_project.Chap109.Lemma_109_4_1_Groupoids

/-!
# Lemma 109.4.1

The morphism PolarizedCurves ⟶ Polarized is an open and closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Lemma 109.4.1: the morphism PolarizedCurves ⟶ Polarized is an open and
closed immersion. -/
@[stacks 0DPZ]
theorem inclusionHom_isOpenAndClosedImmersion :
    OpenImmersion inclusionHom ∧ ClosedImmersion inclusionHom :=
  sorry

/-- The inclusion PolarizedCurves ⟶ Polarized is an open immersion of
categories fibred in groupoids over Spec ℤ. -/
instance instOpenImmersion_inclusionHom : OpenImmersion inclusionHom :=
  sorry

/-- The inclusion PolarizedCurves ⟶ Polarized is a closed immersion of
categories fibred in groupoids over Spec ℤ. -/
instance instClosedImmersion_inclusionHom : ClosedImmersion inclusionHom :=
  sorry

end AlgebraicGeometry.PolarizedCurves
