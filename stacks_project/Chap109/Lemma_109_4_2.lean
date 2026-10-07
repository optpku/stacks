module

public import stacks_project.Chap108.Lemma_108_8_5_Smooth
public import stacks_project.Chap109.Lemma_109_4_2_Forget
public import stacks_project.Chap109.Lemma_109_4_2_Surjective

/-!
# Lemma 109.4.2

The morphism PolarizedCurves ⟶ Curves is smooth and surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Lemma 109.4.2 (1): the morphism PolarizedCurves ⟶ Curves is smooth. -/
@[stacks 0DQ0]
instance instSmooth_toCurvesHom : CohStack.Hom.Smooth toCurvesHom :=
  sorry

/-- Lemma 109.4.2 (2): the morphism PolarizedCurves ⟶ Curves is surjective. -/
@[stacks 0DQ0]
instance instSurjective_toCurvesHom : CohStack.Hom.Surjective toCurvesHom :=
  sorry

end AlgebraicGeometry.PolarizedCurves
