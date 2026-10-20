module

public import ReasLib.AlgebraicGeometry.PolarizedCurves.ToCurves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap109.Lemma_109_4_2_Surjective

/-!
# Lemma 109.4.2

The forgetful 1-morphism `PolarizedCurves ⟶ Curves` is smooth and surjective.
Smoothness is `CohStack.Hom.Smooth` (a smooth surjective algebraic-space presentation with
smooth top arrow, Stacks 075U) and surjectivity is `CohStack.Hom.Surjective` (surjectivity on
points, allowing field extensions, Stacks 04ZS).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Lemma 109.4.2 (1): the 1-morphism PolarizedCurves ⟶ Curves is smooth. -/
@[stacks 0DQ0]
instance instSmooth_toCurvesHom : CohStack.Hom.Smooth (toCurvesHom.{u}) :=
  sorry

/-- Lemma 109.4.2 (2): the 1-morphism PolarizedCurves ⟶ Curves is surjective. -/
@[stacks 0DQ0]
instance instSurjective_toCurvesHom : CohStack.Hom.Surjective (toCurvesHom.{u}) :=
  sorry

end AlgebraicGeometry.PolarizedCurves
