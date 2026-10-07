module

public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_8_1_Constructible
public import stacks_project.Chap66.Lemma_66_20_5_RingSheafSupport

/-!
# Closedness of the support of a sheaf of rings

On the small étale site of an algebraic space, the support of a sheaf of rings is a
closed subset of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.20.5: the support of a sheaf of rings on the small étale site of an algebraic
space is closed. -/
@[stacks 04KC]
theorem isClosed_ringSheafSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (τ : TopologicalSpace (Points X)) (atlas : Points.OpenQuotientAtlas X τ)
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    @IsClosed (Points X) τ (ringSheafSupport F) :=
  sorry

/-- Inverse images of the support of a sheaf of rings along étale morphisms from schemes are
closed. -/
theorem isClosed_schemePreimage_ringSheafSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) RingCat.{u}) {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) :
    IsClosed (schemePreimage f (ringSheafSupport F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
